def shrxl1 : instruction :=
  definst "shrxl" $ do
    pattern fun (v_3095 : reg (bv 32)) (v_3096 : reg (bv 32)) (v_3097 : reg (bv 32)) => do
      v_5388 <- getRegister v_3096;
      v_5389 <- getRegister v_3095;
      setRegister (lhs.of_reg v_3097) (lshr v_5388 (bv_and v_5389 (expression.bv_nat 32 31)));
      pure ()
    pat_end;
    pattern fun (v_3086 : reg (bv 32)) (v_3085 : Mem) (v_3087 : reg (bv 32)) => do
      v_8470 <- evaluateAddress v_3085;
      v_8471 <- load v_8470 4;
      v_8472 <- getRegister v_3086;
      setRegister (lhs.of_reg v_3087) (lshr v_8471 (bv_and v_8472 (expression.bv_nat 32 31)));
      pure ()
    pat_end
