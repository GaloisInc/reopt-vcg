def vpbroadcastw1 : instruction :=
  definst "vpbroadcastw" $ do
    pattern fun (v_2805 : reg (bv 128)) (v_2806 : reg (bv 128)) => do
      v_6986 <- getRegister v_2805;
      v_6987 <- eval (extract v_6986 112 128);
      setRegister (lhs.of_reg v_2806) (concat v_6987 (concat v_6987 (concat v_6987 (concat v_6987 (concat v_6987 (concat v_6987 (concat v_6987 v_6987)))))));
      pure ()
    pat_end;
    pattern fun (v_2815 : reg (bv 128)) (v_2813 : reg (bv 256)) => do
      v_7000 <- getRegister v_2815;
      v_7001 <- eval (extract v_7000 112 128);
      setRegister (lhs.of_reg v_2813) (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 (concat v_7001 v_7001)))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2800 : Mem) (v_2801 : reg (bv 128)) => do
      v_15611 <- evaluateAddress v_2800;
      v_15612 <- load v_15611 2;
      setRegister (lhs.of_reg v_2801) (concat v_15612 (concat v_15612 (concat v_15612 (concat v_15612 (concat v_15612 (concat v_15612 (concat v_15612 v_15612)))))));
      pure ()
    pat_end;
    pattern fun (v_2809 : Mem) (v_2810 : reg (bv 256)) => do
      v_15621 <- evaluateAddress v_2809;
      v_15622 <- load v_15621 2;
      setRegister (lhs.of_reg v_2810) (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 (concat v_15622 v_15622)))))))))))))));
      pure ()
    pat_end
