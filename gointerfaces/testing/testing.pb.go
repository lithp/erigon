// Code generated by protoc-gen-go. DO NOT EDIT.
// versions:
// 	protoc-gen-go v1.26.0
// 	protoc        v3.17.3
// source: testing/testing.proto

package testing

import (
	protoreflect "google.golang.org/protobuf/reflect/protoreflect"
	protoimpl "google.golang.org/protobuf/runtime/protoimpl"
	emptypb "google.golang.org/protobuf/types/known/emptypb"
	reflect "reflect"
	sync "sync"
)

const (
	// Verify that this generated code is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(20 - protoimpl.MinVersion)
	// Verify that runtime/protoimpl is sufficiently up-to-date.
	_ = protoimpl.EnforceVersion(protoimpl.MaxVersion - 20)
)

type TestCaseNumber struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	Count uint64 `protobuf:"varint,1,opt,name=count,proto3" json:"count,omitempty"`
}

func (x *TestCaseNumber) Reset() {
	*x = TestCaseNumber{}
	if protoimpl.UnsafeEnabled {
		mi := &file_testing_testing_proto_msgTypes[0]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *TestCaseNumber) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*TestCaseNumber) ProtoMessage() {}

func (x *TestCaseNumber) ProtoReflect() protoreflect.Message {
	mi := &file_testing_testing_proto_msgTypes[0]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use TestCaseNumber.ProtoReflect.Descriptor instead.
func (*TestCaseNumber) Descriptor() ([]byte, []int) {
	return file_testing_testing_proto_rawDescGZIP(), []int{0}
}

func (x *TestCaseNumber) GetCount() uint64 {
	if x != nil {
		return x.Count
	}
	return 0
}

type TestReport struct {
	state         protoimpl.MessageState
	sizeCache     protoimpl.SizeCache
	unknownFields protoimpl.UnknownFields

	// End of test signal
	End bool `protobuf:"varint,1,opt,name=end,proto3" json:"end,omitempty"`
	// Indication whether the report is about success of part of the test, or failure
	Success bool   `protobuf:"varint,2,opt,name=success,proto3" json:"success,omitempty"`
	Log     string `protobuf:"bytes,3,opt,name=log,proto3" json:"log,omitempty"`
}

func (x *TestReport) Reset() {
	*x = TestReport{}
	if protoimpl.UnsafeEnabled {
		mi := &file_testing_testing_proto_msgTypes[1]
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		ms.StoreMessageInfo(mi)
	}
}

func (x *TestReport) String() string {
	return protoimpl.X.MessageStringOf(x)
}

func (*TestReport) ProtoMessage() {}

func (x *TestReport) ProtoReflect() protoreflect.Message {
	mi := &file_testing_testing_proto_msgTypes[1]
	if protoimpl.UnsafeEnabled && x != nil {
		ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
		if ms.LoadMessageInfo() == nil {
			ms.StoreMessageInfo(mi)
		}
		return ms
	}
	return mi.MessageOf(x)
}

// Deprecated: Use TestReport.ProtoReflect.Descriptor instead.
func (*TestReport) Descriptor() ([]byte, []int) {
	return file_testing_testing_proto_rawDescGZIP(), []int{1}
}

func (x *TestReport) GetEnd() bool {
	if x != nil {
		return x.End
	}
	return false
}

func (x *TestReport) GetSuccess() bool {
	if x != nil {
		return x.Success
	}
	return false
}

func (x *TestReport) GetLog() string {
	if x != nil {
		return x.Log
	}
	return ""
}

var File_testing_testing_proto protoreflect.FileDescriptor

var file_testing_testing_proto_rawDesc = []byte{
	0x0a, 0x15, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67, 0x2f, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e,
	0x67, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x12, 0x07, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67,
	0x1a, 0x1b, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2f, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x62, 0x75,
	0x66, 0x2f, 0x65, 0x6d, 0x70, 0x74, 0x79, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x22, 0x26, 0x0a,
	0x0e, 0x54, 0x65, 0x73, 0x74, 0x43, 0x61, 0x73, 0x65, 0x4e, 0x75, 0x6d, 0x62, 0x65, 0x72, 0x12,
	0x14, 0x0a, 0x05, 0x63, 0x6f, 0x75, 0x6e, 0x74, 0x18, 0x01, 0x20, 0x01, 0x28, 0x04, 0x52, 0x05,
	0x63, 0x6f, 0x75, 0x6e, 0x74, 0x22, 0x4a, 0x0a, 0x0a, 0x54, 0x65, 0x73, 0x74, 0x52, 0x65, 0x70,
	0x6f, 0x72, 0x74, 0x12, 0x10, 0x0a, 0x03, 0x65, 0x6e, 0x64, 0x18, 0x01, 0x20, 0x01, 0x28, 0x08,
	0x52, 0x03, 0x65, 0x6e, 0x64, 0x12, 0x18, 0x0a, 0x07, 0x73, 0x75, 0x63, 0x63, 0x65, 0x73, 0x73,
	0x18, 0x02, 0x20, 0x01, 0x28, 0x08, 0x52, 0x07, 0x73, 0x75, 0x63, 0x63, 0x65, 0x73, 0x73, 0x12,
	0x10, 0x0a, 0x03, 0x6c, 0x6f, 0x67, 0x18, 0x03, 0x20, 0x01, 0x28, 0x09, 0x52, 0x03, 0x6c, 0x6f,
	0x67, 0x32, 0x8f, 0x01, 0x0a, 0x0a, 0x54, 0x65, 0x73, 0x74, 0x44, 0x72, 0x69, 0x76, 0x65, 0x72,
	0x12, 0x40, 0x0a, 0x0d, 0x54, 0x65, 0x73, 0x74, 0x43, 0x61, 0x73, 0x65, 0x43, 0x6f, 0x75, 0x6e,
	0x74, 0x12, 0x16, 0x2e, 0x67, 0x6f, 0x6f, 0x67, 0x6c, 0x65, 0x2e, 0x70, 0x72, 0x6f, 0x74, 0x6f,
	0x62, 0x75, 0x66, 0x2e, 0x45, 0x6d, 0x70, 0x74, 0x79, 0x1a, 0x17, 0x2e, 0x74, 0x65, 0x73, 0x74,
	0x69, 0x6e, 0x67, 0x2e, 0x54, 0x65, 0x73, 0x74, 0x43, 0x61, 0x73, 0x65, 0x4e, 0x75, 0x6d, 0x62,
	0x65, 0x72, 0x12, 0x3f, 0x0a, 0x0d, 0x53, 0x74, 0x61, 0x72, 0x74, 0x54, 0x65, 0x73, 0x74, 0x43,
	0x61, 0x73, 0x65, 0x12, 0x17, 0x2e, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67, 0x2e, 0x54, 0x65,
	0x73, 0x74, 0x43, 0x61, 0x73, 0x65, 0x4e, 0x75, 0x6d, 0x62, 0x65, 0x72, 0x1a, 0x13, 0x2e, 0x74,
	0x65, 0x73, 0x74, 0x69, 0x6e, 0x67, 0x2e, 0x54, 0x65, 0x73, 0x74, 0x52, 0x65, 0x70, 0x6f, 0x72,
	0x74, 0x30, 0x01, 0x42, 0x13, 0x5a, 0x11, 0x2e, 0x2f, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67,
	0x3b, 0x74, 0x65, 0x73, 0x74, 0x69, 0x6e, 0x67, 0x62, 0x06, 0x70, 0x72, 0x6f, 0x74, 0x6f, 0x33,
}

var (
	file_testing_testing_proto_rawDescOnce sync.Once
	file_testing_testing_proto_rawDescData = file_testing_testing_proto_rawDesc
)

func file_testing_testing_proto_rawDescGZIP() []byte {
	file_testing_testing_proto_rawDescOnce.Do(func() {
		file_testing_testing_proto_rawDescData = protoimpl.X.CompressGZIP(file_testing_testing_proto_rawDescData)
	})
	return file_testing_testing_proto_rawDescData
}

var file_testing_testing_proto_msgTypes = make([]protoimpl.MessageInfo, 2)
var file_testing_testing_proto_goTypes = []interface{}{
	(*TestCaseNumber)(nil), // 0: testing.TestCaseNumber
	(*TestReport)(nil),     // 1: testing.TestReport
	(*emptypb.Empty)(nil),  // 2: google.protobuf.Empty
}
var file_testing_testing_proto_depIdxs = []int32{
	2, // 0: testing.TestDriver.TestCaseCount:input_type -> google.protobuf.Empty
	0, // 1: testing.TestDriver.StartTestCase:input_type -> testing.TestCaseNumber
	0, // 2: testing.TestDriver.TestCaseCount:output_type -> testing.TestCaseNumber
	1, // 3: testing.TestDriver.StartTestCase:output_type -> testing.TestReport
	2, // [2:4] is the sub-list for method output_type
	0, // [0:2] is the sub-list for method input_type
	0, // [0:0] is the sub-list for extension type_name
	0, // [0:0] is the sub-list for extension extendee
	0, // [0:0] is the sub-list for field type_name
}

func init() { file_testing_testing_proto_init() }
func file_testing_testing_proto_init() {
	if File_testing_testing_proto != nil {
		return
	}
	if !protoimpl.UnsafeEnabled {
		file_testing_testing_proto_msgTypes[0].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*TestCaseNumber); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
		file_testing_testing_proto_msgTypes[1].Exporter = func(v interface{}, i int) interface{} {
			switch v := v.(*TestReport); i {
			case 0:
				return &v.state
			case 1:
				return &v.sizeCache
			case 2:
				return &v.unknownFields
			default:
				return nil
			}
		}
	}
	type x struct{}
	out := protoimpl.TypeBuilder{
		File: protoimpl.DescBuilder{
			GoPackagePath: reflect.TypeOf(x{}).PkgPath(),
			RawDescriptor: file_testing_testing_proto_rawDesc,
			NumEnums:      0,
			NumMessages:   2,
			NumExtensions: 0,
			NumServices:   1,
		},
		GoTypes:           file_testing_testing_proto_goTypes,
		DependencyIndexes: file_testing_testing_proto_depIdxs,
		MessageInfos:      file_testing_testing_proto_msgTypes,
	}.Build()
	File_testing_testing_proto = out.File
	file_testing_testing_proto_rawDesc = nil
	file_testing_testing_proto_goTypes = nil
	file_testing_testing_proto_depIdxs = nil
}
