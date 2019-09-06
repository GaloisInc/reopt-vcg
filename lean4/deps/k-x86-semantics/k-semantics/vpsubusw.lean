def vpsubusw1 : instruction :=
  definst "vpsubusw" $ do
    pattern fun (v_2609 : reg (bv 128)) (v_2610 : reg (bv 128)) (v_2611 : reg (bv 128)) => do
      v_5674 <- getRegister v_2610;
      v_5677 <- getRegister v_2609;
      v_5680 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 0 16)) (concat (expression.bv_nat 2 0) (extract v_5677 0 16)));
      v_5690 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 16 32)) (concat (expression.bv_nat 2 0) (extract v_5677 16 32)));
      v_5700 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 32 48)) (concat (expression.bv_nat 2 0) (extract v_5677 32 48)));
      v_5710 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 48 64)) (concat (expression.bv_nat 2 0) (extract v_5677 48 64)));
      v_5720 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 64 80)) (concat (expression.bv_nat 2 0) (extract v_5677 64 80)));
      v_5730 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 80 96)) (concat (expression.bv_nat 2 0) (extract v_5677 80 96)));
      v_5740 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 96 112)) (concat (expression.bv_nat 2 0) (extract v_5677 96 112)));
      v_5750 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5674 112 128)) (concat (expression.bv_nat 2 0) (extract v_5677 112 128)));
      setRegister (lhs.of_reg v_2611) (concat (mux (sgt v_5680 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5680 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5680 2 18))) (concat (mux (sgt v_5690 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5690 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5690 2 18))) (concat (mux (sgt v_5700 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5700 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5700 2 18))) (concat (mux (sgt v_5710 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5710 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5710 2 18))) (concat (mux (sgt v_5720 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5720 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5720 2 18))) (concat (mux (sgt v_5730 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5730 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5730 2 18))) (concat (mux (sgt v_5740 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5740 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5740 2 18))) (mux (sgt v_5750 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5750 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5750 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_2620 : reg (bv 256)) (v_2621 : reg (bv 256)) (v_2622 : reg (bv 256)) => do
      v_5769 <- getRegister v_2621;
      v_5772 <- getRegister v_2620;
      v_5775 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 0 16)) (concat (expression.bv_nat 2 0) (extract v_5772 0 16)));
      v_5785 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 16 32)) (concat (expression.bv_nat 2 0) (extract v_5772 16 32)));
      v_5795 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 32 48)) (concat (expression.bv_nat 2 0) (extract v_5772 32 48)));
      v_5805 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 48 64)) (concat (expression.bv_nat 2 0) (extract v_5772 48 64)));
      v_5815 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 64 80)) (concat (expression.bv_nat 2 0) (extract v_5772 64 80)));
      v_5825 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 80 96)) (concat (expression.bv_nat 2 0) (extract v_5772 80 96)));
      v_5835 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 96 112)) (concat (expression.bv_nat 2 0) (extract v_5772 96 112)));
      v_5845 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 112 128)) (concat (expression.bv_nat 2 0) (extract v_5772 112 128)));
      v_5855 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 128 144)) (concat (expression.bv_nat 2 0) (extract v_5772 128 144)));
      v_5865 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 144 160)) (concat (expression.bv_nat 2 0) (extract v_5772 144 160)));
      v_5875 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 160 176)) (concat (expression.bv_nat 2 0) (extract v_5772 160 176)));
      v_5885 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 176 192)) (concat (expression.bv_nat 2 0) (extract v_5772 176 192)));
      v_5895 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 192 208)) (concat (expression.bv_nat 2 0) (extract v_5772 192 208)));
      v_5905 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 208 224)) (concat (expression.bv_nat 2 0) (extract v_5772 208 224)));
      v_5915 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 224 240)) (concat (expression.bv_nat 2 0) (extract v_5772 224 240)));
      v_5925 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5769 240 256)) (concat (expression.bv_nat 2 0) (extract v_5772 240 256)));
      setRegister (lhs.of_reg v_2622) (concat (mux (sgt v_5775 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5775 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5775 2 18))) (concat (mux (sgt v_5785 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5785 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5785 2 18))) (concat (mux (sgt v_5795 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5795 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5795 2 18))) (concat (mux (sgt v_5805 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5805 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5805 2 18))) (concat (mux (sgt v_5815 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5815 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5815 2 18))) (concat (mux (sgt v_5825 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5825 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5825 2 18))) (concat (mux (sgt v_5835 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5835 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5835 2 18))) (concat (mux (sgt v_5845 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5845 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5845 2 18))) (concat (mux (sgt v_5855 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5855 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5855 2 18))) (concat (mux (sgt v_5865 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5865 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5865 2 18))) (concat (mux (sgt v_5875 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5875 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5875 2 18))) (concat (mux (sgt v_5885 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5885 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5885 2 18))) (concat (mux (sgt v_5895 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5895 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5895 2 18))) (concat (mux (sgt v_5905 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5905 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5905 2 18))) (concat (mux (sgt v_5915 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5915 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5915 2 18))) (mux (sgt v_5925 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5925 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5925 2 18))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) (v_2604 : reg (bv 128)) (v_2605 : reg (bv 128)) => do
      v_11786 <- getRegister v_2604;
      v_11789 <- evaluateAddress v_2603;
      v_11790 <- load v_11789 16;
      v_11793 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 0 16)) (concat (expression.bv_nat 2 0) (extract v_11790 0 16)));
      v_11803 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 16 32)) (concat (expression.bv_nat 2 0) (extract v_11790 16 32)));
      v_11813 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 32 48)) (concat (expression.bv_nat 2 0) (extract v_11790 32 48)));
      v_11823 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 48 64)) (concat (expression.bv_nat 2 0) (extract v_11790 48 64)));
      v_11833 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 64 80)) (concat (expression.bv_nat 2 0) (extract v_11790 64 80)));
      v_11843 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 80 96)) (concat (expression.bv_nat 2 0) (extract v_11790 80 96)));
      v_11853 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 96 112)) (concat (expression.bv_nat 2 0) (extract v_11790 96 112)));
      v_11863 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11786 112 128)) (concat (expression.bv_nat 2 0) (extract v_11790 112 128)));
      setRegister (lhs.of_reg v_2605) (concat (mux (sgt v_11793 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11793 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11793 2 18))) (concat (mux (sgt v_11803 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11803 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11803 2 18))) (concat (mux (sgt v_11813 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11813 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11813 2 18))) (concat (mux (sgt v_11823 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11823 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11823 2 18))) (concat (mux (sgt v_11833 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11833 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11833 2 18))) (concat (mux (sgt v_11843 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11843 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11843 2 18))) (concat (mux (sgt v_11853 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11853 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11853 2 18))) (mux (sgt v_11863 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11863 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11863 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_2614 : Mem) (v_2615 : reg (bv 256)) (v_2616 : reg (bv 256)) => do
      v_11877 <- getRegister v_2615;
      v_11880 <- evaluateAddress v_2614;
      v_11881 <- load v_11880 32;
      v_11884 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 0 16)) (concat (expression.bv_nat 2 0) (extract v_11881 0 16)));
      v_11894 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 16 32)) (concat (expression.bv_nat 2 0) (extract v_11881 16 32)));
      v_11904 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 32 48)) (concat (expression.bv_nat 2 0) (extract v_11881 32 48)));
      v_11914 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 48 64)) (concat (expression.bv_nat 2 0) (extract v_11881 48 64)));
      v_11924 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 64 80)) (concat (expression.bv_nat 2 0) (extract v_11881 64 80)));
      v_11934 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 80 96)) (concat (expression.bv_nat 2 0) (extract v_11881 80 96)));
      v_11944 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 96 112)) (concat (expression.bv_nat 2 0) (extract v_11881 96 112)));
      v_11954 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 112 128)) (concat (expression.bv_nat 2 0) (extract v_11881 112 128)));
      v_11964 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 128 144)) (concat (expression.bv_nat 2 0) (extract v_11881 128 144)));
      v_11974 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 144 160)) (concat (expression.bv_nat 2 0) (extract v_11881 144 160)));
      v_11984 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 160 176)) (concat (expression.bv_nat 2 0) (extract v_11881 160 176)));
      v_11994 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 176 192)) (concat (expression.bv_nat 2 0) (extract v_11881 176 192)));
      v_12004 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 192 208)) (concat (expression.bv_nat 2 0) (extract v_11881 192 208)));
      v_12014 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 208 224)) (concat (expression.bv_nat 2 0) (extract v_11881 208 224)));
      v_12024 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 224 240)) (concat (expression.bv_nat 2 0) (extract v_11881 224 240)));
      v_12034 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11877 240 256)) (concat (expression.bv_nat 2 0) (extract v_11881 240 256)));
      setRegister (lhs.of_reg v_2616) (concat (mux (sgt v_11884 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11884 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11884 2 18))) (concat (mux (sgt v_11894 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11894 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11894 2 18))) (concat (mux (sgt v_11904 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11904 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11904 2 18))) (concat (mux (sgt v_11914 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11914 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11914 2 18))) (concat (mux (sgt v_11924 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11924 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11924 2 18))) (concat (mux (sgt v_11934 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11934 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11934 2 18))) (concat (mux (sgt v_11944 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11944 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11944 2 18))) (concat (mux (sgt v_11954 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11954 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11954 2 18))) (concat (mux (sgt v_11964 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11964 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11964 2 18))) (concat (mux (sgt v_11974 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11974 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11974 2 18))) (concat (mux (sgt v_11984 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11984 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11984 2 18))) (concat (mux (sgt v_11994 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11994 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11994 2 18))) (concat (mux (sgt v_12004 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_12004 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_12004 2 18))) (concat (mux (sgt v_12014 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_12014 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_12014 2 18))) (concat (mux (sgt v_12024 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_12024 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_12024 2 18))) (mux (sgt v_12034 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_12034 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_12034 2 18))))))))))))))))));
      pure ()
    pat_end
