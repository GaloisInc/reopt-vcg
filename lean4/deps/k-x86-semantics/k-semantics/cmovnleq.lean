def cmovnleq1 : instruction :=
  definst "cmovnleq" $ do
    pattern fun (v_2942 : reg (bv 64)) (v_2943 : reg (bv 64)) => do
      v_4784 <- getRegister zf;
      v_4787 <- getRegister sf;
      v_4789 <- getRegister of;
      v_4793 <- getRegister v_2942;
      v_4794 <- getRegister v_2943;
      setRegister (lhs.of_reg v_2943) (mux (bit_and (notBool_ (eq v_4784 (expression.bv_nat 1 1))) (eq (eq v_4787 (expression.bv_nat 1 1)) (eq v_4789 (expression.bv_nat 1 1)))) v_4793 v_4794);
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) (v_2938 : reg (bv 64)) => do
      v_8357 <- getRegister zf;
      v_8360 <- getRegister sf;
      v_8362 <- getRegister of;
      v_8366 <- evaluateAddress v_2937;
      v_8367 <- load v_8366 8;
      v_8368 <- getRegister v_2938;
      setRegister (lhs.of_reg v_2938) (mux (bit_and (notBool_ (eq v_8357 (expression.bv_nat 1 1))) (eq (eq v_8360 (expression.bv_nat 1 1)) (eq v_8362 (expression.bv_nat 1 1)))) v_8367 v_8368);
      pure ()
    pat_end
