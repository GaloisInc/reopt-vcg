def vpbroadcastw1 : instruction :=
  definst "vpbroadcastw" $ do
    pattern fun (v_2751 : reg (bv 128)) (v_2752 : reg (bv 128)) => do
      v_7085 <- getRegister v_2751;
      v_7086 <- eval (extract v_7085 112 128);
      setRegister (lhs.of_reg v_2752) (concat v_7086 (concat v_7086 (concat v_7086 (concat v_7086 (concat v_7086 (concat v_7086 (concat v_7086 v_7086)))))));
      pure ()
    pat_end;
    pattern fun (v_2760 : reg (bv 128)) (v_2764 : reg (bv 256)) => do
      v_7099 <- getRegister v_2760;
      v_7100 <- eval (extract v_7099 112 128);
      setRegister (lhs.of_reg v_2764) (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 (concat v_7100 v_7100)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) (v_2747 : reg (bv 128)) => do
      v_15958 <- evaluateAddress v_2750;
      v_15959 <- load v_15958 2;
      setRegister (lhs.of_reg v_2747) (concat v_15959 (concat v_15959 (concat v_15959 (concat v_15959 (concat v_15959 (concat v_15959 (concat v_15959 v_15959)))))));
      pure ()
    pat_end;
    pattern fun (v_2758 : Mem) (v_2759 : reg (bv 256)) => do
      v_15968 <- evaluateAddress v_2758;
      v_15969 <- load v_15968 2;
      setRegister (lhs.of_reg v_2759) (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 (concat v_15969 v_15969)))))))))))))));
      pure ()
    pat_end
