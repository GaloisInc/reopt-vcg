def pandn1 : instruction :=
  definst "pandn" $ do
    pattern fun (v_3215 : reg (bv 128)) (v_3216 : reg (bv 128)) => do
      v_6401 <- getRegister v_3216;
      v_6403 <- getRegister v_3215;
      setRegister (lhs.of_reg v_3216) (bv_and (bv_xor v_6401 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_6403);
      pure ()
    pat_end;
    pattern fun (v_3211 : Mem) (v_3212 : reg (bv 128)) => do
      v_10454 <- getRegister v_3212;
      v_10456 <- evaluateAddress v_3211;
      v_10457 <- load v_10456 16;
      setRegister (lhs.of_reg v_3212) (bv_and (bv_xor v_10454 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_10457);
      pure ()
    pat_end
