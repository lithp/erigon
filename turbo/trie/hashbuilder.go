package trie

import (
	"bytes"
	"fmt"
	"io"
	"math/bits"

	"github.com/holiman/uint256"
	"golang.org/x/crypto/sha3"

	"github.com/ledgerwatch/turbo-geth/common"
	"github.com/ledgerwatch/turbo-geth/core/types/accounts"
	"github.com/ledgerwatch/turbo-geth/crypto"
	"github.com/ledgerwatch/turbo-geth/rlp"
	"github.com/ledgerwatch/turbo-geth/turbo/rlphacks"
)

const hashStackStride = common.HashLength + 1 // + 1 byte for RLP encoding

var EmptyCodeHash = crypto.Keccak256Hash(nil)


type HBuilder interface {
	StructInfoReceiver
	Reset()
	RootHash() (common.Hash, error)
	SetTrace(bool)
	HasRoot() bool
}

// HashBuilder implements the interface `structInfoReceiver` and opcodes that the structural information of the trie
// is comprised of
// DESCRIBED: docs/programmers_guide/guide.md#separation-of-keys-and-the-structure
type HashBuilder struct {
	byteArrayWriter *ByteArrayWriter

	HashStack []byte                // Stack of sub-slices, each 33 bytes each, containing RLP encodings of node hashes (or of nodes themselves, if shorter than 32 bytes)
	NodeStack []node                // Stack of nodes
	acc       accounts.Account      // Working account instance (to avoid extra allocations)
	sha       keccakState           // Keccak primitive that can absorb data (Write), and get squeezed to the hash out (Read)
	hashBuf   [hashStackStride]byte // RLP representation of hash (or un-hashes value)
	keyPrefix [1]byte
	lenPrefix [4]byte
	valBuf    [128]byte // Enough to accommodate hash encoding of any account
	b         [1]byte   // Buffer for single byte
	prefixBuf [8]byte
	trace     bool // Set to true when HashBuilder is required to print trace information for diagnostics
	NodeLen int
}

// NewHashBuilder creates a new HashBuilder
func NewHashBuilder(trace bool) *HashBuilder {
	return &HashBuilder{
		sha:             sha3.NewLegacyKeccak256().(keccakState),
		byteArrayWriter: &ByteArrayWriter{},
		trace:           trace,
	}
}

func (hb *HashBuilder) SetTrace(trace bool) {
	hb.trace = trace
}

// Reset makes the HashBuilder suitable for reuse
func (hb *HashBuilder) Reset() {
	if len(hb.HashStack) > 0 {
		hb.HashStack = hb.HashStack[:0]
	}
	if len(hb.NodeStack) > 0 {
		hb.NodeStack = hb.NodeStack[:0]
	}
}

func (hb *HashBuilder) Leaf(length int, keyHex []byte, val rlphacks.RlpSerializable) error {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("LEAF %d\n", length)
	}
	if length < 0 {
		return fmt.Errorf("length %d", length)
	}
	key := keyHex[len(keyHex)-length:]
	s := &shortNode{Key: common.CopyBytes(key), Val: valueNode(common.CopyBytes(val.RawBytes()))}
	hb.NodeStack = append(hb.NodeStack, s)
	if err := hb.leafHashWithKeyVal(key, val); err != nil {
		return err
	}
	copy(s.ref.data[:], hb.HashStack[len(hb.HashStack)-common.HashLength:])
	s.ref.len = hb.HashStack[len(hb.HashStack)-common.HashLength-1] - 0x80
	if s.ref.len > 32 {
		s.ref.len = hb.HashStack[len(hb.HashStack)-common.HashLength-1] - 0xc0 + 1
		copy(s.ref.data[:], hb.HashStack[len(hb.HashStack)-common.HashLength-1:])
	}
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}
	return nil
}

// To be called internally
func (hb *HashBuilder) leafHashWithKeyVal(key []byte, val rlphacks.RlpSerializable) error {
	// Compute the total length of binary representation
	var kp, kl int
	// Write key
	var compactLen int
	var ni int
	var compact0 byte
	if hasTerm(key) {
		compactLen = (len(key)-1)/2 + 1
		if len(key)&1 == 0 {
			compact0 = 0x30 + key[0] // Odd: (3<<4) + first nibble
			ni = 1
		} else {
			compact0 = 0x20
		}
	} else {
		compactLen = len(key)/2 + 1
		if len(key)&1 == 1 {
			compact0 = 0x10 + key[0] // Odd: (1<<4) + first nibble
			ni = 1
		}
	}
	if compactLen > 1 {
		hb.keyPrefix[0] = 0x80 + byte(compactLen)
		kp = 1
		kl = compactLen
	} else {
		kl = 1
	}

	err := hb.completeLeafHash(kp, kl, compactLen, key, compact0, ni, val)
	if err != nil {
		return err
	}

	hb.HashStack = append(hb.HashStack, hb.hashBuf[:]...)
	if len(hb.HashStack) > hashStackStride*len(hb.NodeStack) {
		hb.NodeStack = append(hb.NodeStack, nil)
	}
	return nil
}

func (hb *HashBuilder) completeLeafHash(kp, kl, compactLen int, key []byte, compact0 byte, ni int, val rlphacks.RlpSerializable) error {
	totalLen := kp + kl + val.DoubleRLPLen()
	pt := rlphacks.GenerateStructLen(hb.lenPrefix[:], totalLen)

	var writer io.Writer
	var reader io.Reader

	if totalLen+pt < common.HashLength {
		// Embedded node
		hb.byteArrayWriter.Setup(hb.hashBuf[:], 0)
		writer = hb.byteArrayWriter
	} else {
		hb.sha.Reset()
		writer = hb.sha
		reader = hb.sha
	}

	if _, err := writer.Write(hb.lenPrefix[:pt]); err != nil {
		return err
	}
	if _, err := writer.Write(hb.keyPrefix[:kp]); err != nil {
		return err
	}
	hb.b[0] = compact0
	if _, err := writer.Write(hb.b[:]); err != nil {
		return err
	}
	for i := 1; i < compactLen; i++ {
		hb.b[0] = key[ni]*16 + key[ni+1]
		if _, err := writer.Write(hb.b[:]); err != nil {
			return err
		}
		ni += 2
	}

	if err := val.ToDoubleRLP(writer, hb.prefixBuf[:]); err != nil {
		return err
	}

	if reader != nil {
		hb.hashBuf[0] = 0x80 + common.HashLength
		if _, err := reader.Read(hb.hashBuf[1:]); err != nil {
			return err
		}
	}

	hb.NodeLen = totalLen
	return nil
}

func (hb *HashBuilder) LeafHash(length int, keyHex []byte, val rlphacks.RlpSerializable) error {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("LEAFHASH %d\n", length)
	}
	if length < 0 {
		return fmt.Errorf("length %d", length)
	}
	key := keyHex[len(keyHex)-length:]
	return hb.leafHashWithKeyVal(key, val)
}

func (hb *HashBuilder) AccountLeaf(length int, keyHex []byte, balance *uint256.Int, nonce uint64, incarnation uint64, fieldSet uint32, accountCodeSize int) (err error) {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("ACCOUNTLEAF %d (%b)\n", length, fieldSet)
	}
	key := keyHex[len(keyHex)-length:]
	copy(hb.acc.Root[:], EmptyRoot[:])
	copy(hb.acc.CodeHash[:], EmptyCodeHash[:])
	hb.acc.Nonce = nonce
	hb.acc.Balance.Set(balance)
	hb.acc.Initialised = true
	hb.acc.Incarnation = incarnation

	popped := 0
	var root node
	if fieldSet&uint32(4) != 0 {
		copy(hb.acc.Root[:], hb.HashStack[len(hb.HashStack)-popped*hashStackStride-common.HashLength:len(hb.HashStack)-popped*hashStackStride])
		if hb.acc.Root != EmptyRoot {
			// Root is on top of the stack
			root = hb.NodeStack[len(hb.NodeStack)-popped-1]
			if root == nil {
				root = hashNode{hash: common.CopyBytes(hb.acc.Root[:])}
			}
		}
		popped++
	}
	var accountCode codeNode
	if fieldSet&uint32(8) != 0 {
		copy(hb.acc.CodeHash[:], hb.HashStack[len(hb.HashStack)-popped*hashStackStride-common.HashLength:len(hb.HashStack)-popped*hashStackStride])
		ok := false
		if !bytes.Equal(hb.acc.CodeHash[:], EmptyCodeHash[:]) {
			stackTop := hb.NodeStack[len(hb.NodeStack)-popped-1]
			if stackTop != nil { // if we don't have any stack top it might be okay because we didn't resolve the code yet (stateful resolver)
				// but if we have something on top of the stack that isn't `nil`, it has to be a codeNode
				accountCode, ok = stackTop.(codeNode)
				if !ok {
					return fmt.Errorf("unexpected node type on the node stack, wanted codeNode, got %T:%s", stackTop, stackTop)
				}
			}
		}
		popped++
	}
	var accCopy accounts.Account
	accCopy.Copy(&hb.acc)

	if !bytes.Equal(accCopy.CodeHash[:], EmptyCodeHash[:]) && accountCode != nil {
		accountCodeSize = len(accountCode)
	}

	a := &accountNode{accCopy, root, true, accountCode, accountCodeSize}
	s := &shortNode{Key: common.CopyBytes(key), Val: a}
	// this invocation will take care of the popping given number of items from both hash stack and node stack,
	// pushing resulting hash to the hash stack, and nil to the node stack
	if err = hb.accountLeafHashWithKey(key, popped); err != nil {
		return err
	}
	copy(s.ref.data[:], hb.HashStack[len(hb.HashStack)-common.HashLength:])
	s.ref.len = 32
	// Replace top of the stack
	hb.NodeStack[len(hb.NodeStack)-1] = s
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))

	}
	return nil
}

func (hb *HashBuilder) AccountLeafHash(length int, keyHex []byte, balance *uint256.Int, nonce uint64, incarnation uint64, fieldSet uint32) (err error) {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("ACCOUNTLEAFHASH %d (%b)\n", length, fieldSet)
	}
	key := keyHex[len(keyHex)-length:]
	hb.acc.Nonce = nonce
	hb.acc.Balance.Set(balance)
	hb.acc.Initialised = true
	hb.acc.Incarnation = incarnation

	popped := 0
	if fieldSet&AccountFieldStorageOnly != 0 {
		copy(hb.acc.Root[:], hb.HashStack[len(hb.HashStack)-popped*hashStackStride-common.HashLength:len(hb.HashStack)-popped*hashStackStride])
		popped++
	} else {
		copy(hb.acc.Root[:], EmptyRoot[:])
	}

	if fieldSet&AccountFieldCodeOnly != 0 {
		copy(hb.acc.CodeHash[:], hb.HashStack[len(hb.HashStack)-popped*hashStackStride-common.HashLength:len(hb.HashStack)-popped*hashStackStride])
		popped++
	} else {
		copy(hb.acc.CodeHash[:], EmptyCodeHash[:])
	}

	return hb.accountLeafHashWithKey(key, popped)
}

// To be called internally
func (hb *HashBuilder) accountLeafHashWithKey(key []byte, popped int) error {
	// Compute the total length of binary representation
	var kp, kl int
	// Write key
	var compactLen int
	var ni int
	var compact0 byte
	if hasTerm(key) {
		compactLen = (len(key)-1)/2 + 1
		if len(key)&1 == 0 {
			compact0 = 48 + key[0] // Odd (1<<4) + first nibble
			ni = 1
		} else {
			compact0 = 32
		}
	} else {
		compactLen = len(key)/2 + 1
		if len(key)&1 == 1 {
			compact0 = 16 + key[0] // Odd (1<<4) + first nibble
			ni = 1
		}
	}
	if compactLen > 1 {
		hb.keyPrefix[0] = byte(128 + compactLen)
		kp = 1
		kl = compactLen
	} else {
		kl = 1
	}
	valLen := hb.acc.EncodingLengthForHashing()
	hb.acc.EncodeForHashing(hb.valBuf[:])
	val := rlphacks.RlpEncodedBytes(hb.valBuf[:valLen])

	err := hb.completeLeafHash(kp, kl, compactLen, key, compact0, ni, val)
	if err != nil {
		return err
	}
	if popped > 0 {
		hb.HashStack = hb.HashStack[:len(hb.HashStack)-popped*hashStackStride]
		hb.NodeStack = hb.NodeStack[:len(hb.NodeStack)-popped]
	}
	hb.HashStack = append(hb.HashStack, hb.hashBuf[:]...)
	hb.NodeStack = append(hb.NodeStack, nil)
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}
	return nil
}

func (hb *HashBuilder) Extension(key []byte) error {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("EXTENSION %x\n", key)
	}
	nd := hb.NodeStack[len(hb.NodeStack)-1]
	var s *shortNode
	switch n := nd.(type) {
	case nil:
		branchHash := common.CopyBytes(hb.HashStack[len(hb.HashStack)-common.HashLength:])
		s = &shortNode{Key: common.CopyBytes(key), Val: hashNode{hash: branchHash}}
	case *fullNode:
		s = &shortNode{Key: common.CopyBytes(key), Val: n}
	default:
		return fmt.Errorf("wrong Val type for an extension: %T", nd)
	}
	hb.NodeStack[len(hb.NodeStack)-1] = s
	if err := hb.ExtensionHash(key); err != nil {
		return err
	}
	copy(s.ref.data[:], hb.HashStack[len(hb.HashStack)-common.HashLength:])
	s.ref.len = 32
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}
	return nil
}

func (hb *HashBuilder) ExtensionHash(key []byte) error {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("EXTENSIONHASH %x\n", key)
	}
	branchHash := hb.HashStack[len(hb.HashStack)-hashStackStride:]
	// Compute the total length of binary representation
	var kp, kl int
	// Write key
	var compactLen int
	var ni int
	var compact0 byte
	// https://github.com/ethereum/wiki/wiki/Patricia-Tree#specification-compact-encoding-of-hex-sequence-with-optional-terminator
	if hasTerm(key) {
		compactLen = (len(key)-1)/2 + 1
		if len(key)&1 == 0 {
			compact0 = 0x30 + key[0] // Odd: (3<<4) + first nibble
			ni = 1
		} else {
			compact0 = 0x20
		}
	} else {
		compactLen = len(key)/2 + 1
		if len(key)&1 == 1 {
			compact0 = 0x10 + key[0] // Odd: (1<<4) + first nibble
			ni = 1
		}
	}
	if compactLen > 1 {
		hb.keyPrefix[0] = 0x80 + byte(compactLen)
		kp = 1
		kl = compactLen
	} else {
		kl = 1
	}
	totalLen := kp + kl + 33
	pt := rlphacks.GenerateStructLen(hb.lenPrefix[:], totalLen)
	hb.sha.Reset()
	if _, err := hb.sha.Write(hb.lenPrefix[:pt]); err != nil {
		return err
	}
	if _, err := hb.sha.Write(hb.keyPrefix[:kp]); err != nil {
		return err
	}
	hb.b[0] = compact0
	if _, err := hb.sha.Write(hb.b[:]); err != nil {
		return err
	}
	for i := 1; i < compactLen; i++ {
		hb.b[0] = key[ni]*16 + key[ni+1]
		if _, err := hb.sha.Write(hb.b[:]); err != nil {
			return err
		}
		ni += 2
	}
	if _, err := hb.sha.Write(branchHash[:common.HashLength+1]); err != nil {
		return err
	}
	// Replace previous hash with the new one
	if _, err := hb.sha.Read(hb.HashStack[len(hb.HashStack)-common.HashLength:]); err != nil {
		return err
	}
	hb.HashStack[len(hb.HashStack)-hashStackStride] = 0x80 + common.HashLength
	if _, ok := hb.NodeStack[len(hb.NodeStack)-1].(*fullNode); ok {
		return fmt.Errorf("extensionHash cannot be emitted when a node is on top of the stack")
	}
	hb.NodeLen = totalLen
	return nil
}

func (hb *HashBuilder) Branch(set uint16) error {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("BRANCH (%b)\n", set)
	}
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}
	f := &fullNode{}
	digits := bits.OnesCount16(set)
	if len(hb.NodeStack) < digits {
		return fmt.Errorf("len(hb.nodeStask) %d < digits %d", len(hb.NodeStack), digits)
	}
	nodes := hb.NodeStack[len(hb.NodeStack)-digits:]
	hashes := hb.HashStack[len(hb.HashStack)-hashStackStride*digits:]
	var i int
	for digit := uint(0); digit < 16; digit++ {
		if ((uint16(1) << digit) & set) != 0 {
			if nodes[i] == nil {
				f.Children[digit] = hashNode{hash: common.CopyBytes(hashes[hashStackStride*i+1 : hashStackStride*(i+1)])}
			} else {
				f.Children[digit] = nodes[i]
			}
			i++
		}
	}
	hb.NodeStack = hb.NodeStack[:len(hb.NodeStack)-digits+1]
	hb.NodeStack[len(hb.NodeStack)-1] = f
	if err := hb.BranchHash(set); err != nil {
		return err
	}
	copy(f.ref.data[:], hb.HashStack[len(hb.HashStack)-common.HashLength:])
	f.ref.len = 32
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}

	return nil
}

func (hb *HashBuilder) BranchHash(set uint16) error {
	hb.NodeLen = 0
	if hb.trace {
		fmt.Printf("BRANCHHASH (%b)\n", set)
	}
	digits := bits.OnesCount16(set)
	if len(hb.HashStack) < hashStackStride*digits {
		return fmt.Errorf("len(hb.HashStack) %d < hashStackStride*digits %d", len(hb.HashStack), hashStackStride*digits)
	}
	hashes := hb.HashStack[len(hb.HashStack)-hashStackStride*digits:]
	// Calculate the size of the resulting RLP
	totalSize := 17 // These are 17 length prefixes
	var i int
	for digit := uint(0); digit < 16; digit++ {
		if ((uint16(1) << digit) & set) != 0 {
			if hashes[hashStackStride*i] == 0x80+common.HashLength {
				totalSize += common.HashLength
			} else {
				// Embedded node
				totalSize += int(hashes[hashStackStride*i] - rlp.EmptyListCode)
			}
			i++
		}
	}
	hb.sha.Reset()
	pt := rlphacks.GenerateStructLen(hb.lenPrefix[:], totalSize)
	if _, err := hb.sha.Write(hb.lenPrefix[:pt]); err != nil {
		return err
	}
	// Output children hashes or embedded RLPs
	i = 0
	hb.b[0] = rlp.EmptyStringCode
	for digit := uint(0); digit < 17; digit++ {
		if ((uint16(1) << digit) & set) != 0 {
			if hashes[hashStackStride*i] == byte(0x80+common.HashLength) {
				if _, err := hb.sha.Write(hashes[hashStackStride*i : hashStackStride*i+hashStackStride]); err != nil {
					return err
				}
			} else {
				// Embedded node
				size := int(hashes[hashStackStride*i]) - rlp.EmptyListCode
				if _, err := hb.sha.Write(hashes[hashStackStride*i : hashStackStride*i+size+1]); err != nil {
					return err
				}
			}
			i++
		} else {
			if _, err := hb.sha.Write(hb.b[:]); err != nil {
				return err
			}
		}
	}
	hb.HashStack = hb.HashStack[:len(hb.HashStack)-hashStackStride*digits+hashStackStride]
	hb.HashStack[len(hb.HashStack)-hashStackStride] = 0x80 + common.HashLength
	if _, err := hb.sha.Read(hb.HashStack[len(hb.HashStack)-common.HashLength:]); err != nil {
		return err
	}

	if hashStackStride*len(hb.NodeStack) > len(hb.HashStack) {
		hb.NodeStack = hb.NodeStack[:len(hb.NodeStack)-digits+1]
		hb.NodeStack[len(hb.NodeStack)-1] = nil
		if hb.trace {
			fmt.Printf("Setting hb.NodeStack[%d] to nil\n", len(hb.NodeStack)-1)
		}
	}
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}
	hb.NodeLen = totalSize
	return nil
}

func (hb *HashBuilder) Hash(hash []byte) error {
	if hb.trace {
		fmt.Printf("HASH\n")
	}
	hb.HashStack = append(hb.HashStack, 0x80+common.HashLength)
	hb.HashStack = append(hb.HashStack, hash...)
	hb.NodeStack = append(hb.NodeStack, nil)
	if hb.trace {
		fmt.Printf("Stack depth: %d\n", len(hb.NodeStack))
	}

	return nil
}

func (hb *HashBuilder) code(code []byte) error {
	if hb.trace {
		fmt.Printf("CODE\n")
	}
	codeCopy := common.CopyBytes(code)
	n := codeNode(codeCopy)
	hb.NodeStack = append(hb.NodeStack, n)
	hb.sha.Reset()
	if _, err := hb.sha.Write(codeCopy); err != nil {
		return err
	}
	var hash [hashStackStride]byte // RLP representation of hash (or un-hashes value)
	hash[0] = 0x80 + common.HashLength
	if _, err := hb.sha.Read(hash[1:]); err != nil {
		return err
	}
	hb.HashStack = append(hb.HashStack, hash[:]...)
	return nil
}

func (hb *HashBuilder) emptyRoot() {
	if hb.trace {
		fmt.Printf("EMPTYROOT\n")
	}
	hb.NodeStack = append(hb.NodeStack, nil)
	var hash [hashStackStride]byte // RLP representation of hash (or un-hashes value)
	hash[0] = 0x80 + common.HashLength
	copy(hash[1:], EmptyRoot[:])
	hb.HashStack = append(hb.HashStack, hash[:]...)
}

func (hb *HashBuilder) RootHash() (common.Hash, error) {
	if !hb.HasRoot() {
		return common.Hash{}, fmt.Errorf("no root in the tree")
	}
	return hb.rootHash(), nil
}

func (hb *HashBuilder) rootHash() common.Hash {
	var hash common.Hash
	copy(hash[:], hb.TopHash())
	return hash
}

func (hb *HashBuilder) TopHash() []byte {
	return hb.HashStack[len(hb.HashStack)-hashStackStride+1:]
}

func (hb *HashBuilder) root() node {
	if hb.trace && len(hb.NodeStack) > 0 {
		fmt.Printf("len(hb.NodeStack)=%d\n", len(hb.NodeStack))
	}
	return hb.NodeStack[len(hb.NodeStack)-1]
}

func (hb *HashBuilder) HasRoot() bool {
	return len(hb.NodeStack) > 0
}
