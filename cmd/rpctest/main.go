package main

import (
	"context"
	"fmt"
	"os"
	"os/signal"
	"syscall"

	"github.com/ledgerwatch/erigon/cmd/rpctest/rpctest"
	"github.com/ledgerwatch/erigon/log"
	"github.com/spf13/cobra"
)

func main() {
	log.SetupDefaultTerminalLogger(log.Lvl(3), "", "")

	var (
		needCompare bool
		fullTest    bool
		gethURL     string
		erigonURL   string
		blockFrom   uint64
		blockTo     uint64
		chaindata   string
		recordFile  string
	)
	withErigonUrl := func(cmd *cobra.Command) {
		cmd.Flags().StringVar(&erigonURL, "erigonUrl", "http://localhost:8545", "Erigon rpcdaemon url")
	}
	withGethUrl := func(cmd *cobra.Command) {
		cmd.Flags().StringVar(&gethURL, "gethUrl", "http://localhost:8546", "geth rpc url")
	}
	withBlockNum := func(cmd *cobra.Command) {
		cmd.Flags().Uint64Var(&blockFrom, "blockFrom", 2000000, "Block number to start test generation from")
		cmd.Flags().Uint64Var(&blockTo, "blockTo", 2101000, "Block number to end test generation at")
	}
	withNeedCompare := func(cmd *cobra.Command) {
		cmd.Flags().BoolVar(&needCompare, "needCompare", false, "need compare with geth")
	}
	withRecord := func(cmd *cobra.Command) {
		cmd.Flags().StringVar(&recordFile, "recordFile", "", "File where to record requests and responses to")
	}
	with := func(cmd *cobra.Command, opts ...func(*cobra.Command)) {
		for i := range opts {
			opts[i](cmd)
		}
	}

	var bench1Cmd = &cobra.Command{
		Use:   "bench1",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench1(erigonURL, gethURL, needCompare, fullTest, blockFrom, blockTo, recordFile)
		},
	}
	with(bench1Cmd, withErigonUrl, withGethUrl, withNeedCompare, withBlockNum, withRecord)
	bench1Cmd.Flags().BoolVar(&fullTest, "fullTest", false, "some text")

	var bench2Cmd = &cobra.Command{
		Use:   "bench2",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench2(erigonURL)
		},
	}
	var bench3Cmd = &cobra.Command{
		Use:   "bench3",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench3(erigonURL, gethURL)
		},
	}
	with(bench3Cmd, withErigonUrl, withGethUrl)

	var bench4Cmd = &cobra.Command{
		Use:   "bench4",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench4(erigonURL)
		},
	}
	with(bench4Cmd, withErigonUrl)

	var bench5Cmd = &cobra.Command{
		Use:   "bench5",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench5(erigonURL)
		},
	}
	with(bench5Cmd, withErigonUrl)
	var bench6Cmd = &cobra.Command{
		Use:   "bench6",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench6(erigonURL)
		},
	}
	with(bench6Cmd, withErigonUrl)

	var bench7Cmd = &cobra.Command{
		Use:   "bench7",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench7(erigonURL, gethURL)
		},
	}
	with(bench7Cmd, withErigonUrl, withGethUrl)

	var bench8Cmd = &cobra.Command{
		Use:   "bench8",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench8(erigonURL, gethURL, needCompare, blockFrom, blockTo, recordFile)
		},
	}
	with(bench8Cmd, withErigonUrl, withGethUrl, withNeedCompare, withBlockNum, withRecord)

	var bench9Cmd = &cobra.Command{
		Use:   "bench9",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench9(erigonURL, gethURL, needCompare)
		},
	}
	with(bench9Cmd, withErigonUrl, withGethUrl, withNeedCompare)

	var bench10Cmd = &cobra.Command{
		Use:   "bench10",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			err := rpctest.Bench10(erigonURL, gethURL, blockFrom, blockTo, recordFile)
			if err != nil {
				log.Error("bench 10 err", "err", err)
			}
		},
	}
	with(bench10Cmd, withGethUrl, withErigonUrl, withBlockNum, withRecord)

	var bench11Cmd = &cobra.Command{
		Use:   "bench11",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench11(erigonURL, gethURL, needCompare, blockFrom, blockTo, recordFile)
		},
	}
	with(bench11Cmd, withGethUrl, withErigonUrl, withNeedCompare, withBlockNum, withRecord)

	var bench12Cmd = &cobra.Command{
		Use:   "bench12",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench12(erigonURL, gethURL, needCompare, blockFrom, blockTo, recordFile)
		},
	}
	with(bench12Cmd, withGethUrl, withErigonUrl, withNeedCompare, withBlockNum, withRecord)

	var bench13Cmd = &cobra.Command{
		Use:   "bench13",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Bench13(erigonURL, gethURL, needCompare, blockFrom, blockTo, recordFile)
		},
	}
	with(bench13Cmd, withGethUrl, withErigonUrl, withNeedCompare, withBlockNum, withRecord)

	var benchTraceBlockCmd = &cobra.Command{
		Use:   "benchTraceBlock",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.BenchTraceBlock(erigonURL, gethURL, needCompare, blockFrom, blockTo, recordFile)
		},
	}
	with(benchTraceBlockCmd, withGethUrl, withErigonUrl, withNeedCompare, withBlockNum, withRecord)

	var benchTraceFilterCmd = &cobra.Command{
		Use:   "benchTraceFilter",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.BenchTraceFilter(erigonURL, gethURL, needCompare, blockFrom, blockTo, recordFile)
		},
	}
	with(benchTraceFilterCmd, withGethUrl, withErigonUrl, withNeedCompare, withBlockNum, withRecord)

	var proofsCmd = &cobra.Command{
		Use:   "proofs",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Proofs(chaindata, gethURL, blockFrom)
		},
	}
	proofsCmd.Flags().StringVar(&chaindata, "chaindata", "", "")
	with(proofsCmd, withGethUrl, withBlockNum)

	var fixStateCmd = &cobra.Command{
		Use:   "fixstate",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.FixState(chaindata, gethURL)
		},
	}
	fixStateCmd.Flags().StringVar(&chaindata, "chaindata", "", "")
	with(fixStateCmd, withGethUrl)

	var replayCmd = &cobra.Command{
		Use:   "replay",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.Replay(erigonURL, recordFile)
		},
	}
	with(replayCmd, withErigonUrl, withRecord)

	var tmpDataDir, tmpDataDirOrig string
	var notRegenerateGethData bool
	var compareAccountRange = &cobra.Command{
		Use:   "compareAccountRange",
		Short: "",
		Long:  ``,
		Run: func(cmd *cobra.Command, args []string) {
			rpctest.CompareAccountRange(erigonURL, gethURL, tmpDataDir, tmpDataDirOrig, blockFrom, notRegenerateGethData)
		},
	}
	with(compareAccountRange, withErigonUrl, withGethUrl, withBlockNum)
	compareAccountRange.Flags().BoolVar(&notRegenerateGethData, "regenGethData", false, "")
	compareAccountRange.Flags().StringVar(&tmpDataDir, "tmpdir", "/media/b00ris/nvme/accrange1", "dir for tmp db")
	compareAccountRange.Flags().StringVar(&tmpDataDirOrig, "gethtmpdir", "/media/b00ris/nvme/accrangeorig1", "dir for tmp db")

	var rootCmd = &cobra.Command{Use: "test"}
	rootCmd.Flags().StringVar(&erigonURL, "erigonUrl", "http://localhost:8545", "Erigon rpcdaemon url")
	rootCmd.Flags().StringVar(&gethURL, "gethUrl", "http://localhost:8546", "geth rpc url")
	rootCmd.Flags().Uint64Var(&blockFrom, "blockFrom", 2000000, "Block number to start test generation from")
	rootCmd.Flags().Uint64Var(&blockTo, "blockTo", 2101000, "Block number to end test generation at")

	rootCmd.AddCommand(
		bench1Cmd,
		bench2Cmd,
		bench3Cmd,
		bench4Cmd,
		bench5Cmd,
		bench6Cmd,
		bench7Cmd,
		bench8Cmd,
		bench9Cmd,
		bench10Cmd,
		bench11Cmd,
		bench12Cmd,
		bench13Cmd,
		benchTraceBlockCmd,
		benchTraceFilterCmd,
		proofsCmd,
		fixStateCmd,
		compareAccountRange,
		replayCmd,
	)
	if err := rootCmd.ExecuteContext(rootContext()); err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
}

func rootContext() context.Context {
	ctx, cancel := context.WithCancel(context.Background())
	go func() {
		ch := make(chan os.Signal, 1)
		signal.Notify(ch, os.Interrupt, syscall.SIGTERM)
		defer signal.Stop(ch)

		select {
		case <-ch:
			log.Info("Got interrupt, shutting down...")
		case <-ctx.Done():
		}

		cancel()
	}()
	return ctx
}
