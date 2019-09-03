def cmovngq1 : instruction :=
  definst "cmovngq" $ do
    pattern fun (v_2915 : reg (bv 64)) (v_2916 : reg (bv 64)) => do
      v_4733 <- getRegister zf;
      v_4735 <- getRegister sf;
      v_4737 <- getRegister of;
      v_4742 <- getRegister v_2915;
      v_4743 <- getRegister v_2916;
      setRegister (lhs.of_reg v_2916) (mux (bit_or (eq v_4733 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4735 (expression.bv_nat 1 1)) (eq v_4737 (expression.bv_nat 1 1))))) v_4742 v_4743);
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) (v_2911 : reg (bv 64)) => do
      v_8315 <- getRegister zf;
      v_8317 <- getRegister sf;
      v_8319 <- getRegister of;
      v_8324 <- evaluateAddress v_2910;
      v_8325 <- load v_8324 8;
      v_8326 <- getRegister v_2911;
      setRegister (lhs.of_reg v_2911) (mux (bit_or (eq v_8315 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8317 (expression.bv_nat 1 1)) (eq v_8319 (expression.bv_nat 1 1))))) v_8325 v_8326);
      pure ()
    pat_end
