def cmovzq1 : instruction :=
  definst "cmovzq" $ do
    pattern fun (v_3350 : reg (bv 64)) (v_3351 : reg (bv 64)) => do
      v_5246 <- getRegister zf;
      v_5248 <- getRegister v_3350;
      v_5249 <- getRegister v_3351;
      setRegister (lhs.of_reg v_3351) (mux (eq v_5246 (expression.bv_nat 1 1)) v_5248 v_5249);
      pure ()
    pat_end;
    pattern fun (v_3345 : Mem) (v_3346 : reg (bv 64)) => do
      v_8618 <- getRegister zf;
      v_8620 <- evaluateAddress v_3345;
      v_8621 <- load v_8620 8;
      v_8622 <- getRegister v_3346;
      setRegister (lhs.of_reg v_3346) (mux (eq v_8618 (expression.bv_nat 1 1)) v_8621 v_8622);
      pure ()
    pat_end
