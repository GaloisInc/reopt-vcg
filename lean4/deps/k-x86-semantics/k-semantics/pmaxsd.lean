def pmaxsd1 : instruction :=
  definst "pmaxsd" $ do
    pattern fun (v_2620 : reg (bv 128)) (v_2621 : reg (bv 128)) => do
      v_4818 <- getRegister v_2621;
      v_4819 <- eval (extract v_4818 0 32);
      v_4820 <- getRegister v_2620;
      v_4821 <- eval (extract v_4820 0 32);
      v_4824 <- eval (extract v_4818 32 64);
      v_4825 <- eval (extract v_4820 32 64);
      v_4828 <- eval (extract v_4818 64 96);
      v_4829 <- eval (extract v_4820 64 96);
      v_4832 <- eval (extract v_4818 96 128);
      v_4833 <- eval (extract v_4820 96 128);
      setRegister (lhs.of_reg v_2621) (concat (mux (sgt v_4819 v_4821) v_4819 v_4821) (concat (mux (sgt v_4824 v_4825) v_4824 v_4825) (concat (mux (sgt v_4828 v_4829) v_4828 v_4829) (mux (sgt v_4832 v_4833) v_4832 v_4833))));
      pure ()
    pat_end;
    pattern fun (v_2617 : Mem) (v_2616 : reg (bv 128)) => do
      v_11719 <- getRegister v_2616;
      v_11720 <- eval (extract v_11719 0 32);
      v_11721 <- evaluateAddress v_2617;
      v_11722 <- load v_11721 16;
      v_11723 <- eval (extract v_11722 0 32);
      v_11726 <- eval (extract v_11719 32 64);
      v_11727 <- eval (extract v_11722 32 64);
      v_11730 <- eval (extract v_11719 64 96);
      v_11731 <- eval (extract v_11722 64 96);
      v_11734 <- eval (extract v_11719 96 128);
      v_11735 <- eval (extract v_11722 96 128);
      setRegister (lhs.of_reg v_2616) (concat (mux (sgt v_11720 v_11723) v_11720 v_11723) (concat (mux (sgt v_11726 v_11727) v_11726 v_11727) (concat (mux (sgt v_11730 v_11731) v_11730 v_11731) (mux (sgt v_11734 v_11735) v_11734 v_11735))));
      pure ()
    pat_end
