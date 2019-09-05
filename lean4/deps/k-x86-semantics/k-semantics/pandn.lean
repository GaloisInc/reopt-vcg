def pandn1 : instruction :=
  definst "pandn" $ do
    pattern fun (v_3266 : reg (bv 128)) (v_3267 : reg (bv 128)) => do
      v_6289 <- getRegister v_3267;
      v_6291 <- getRegister v_3266;
      setRegister (lhs.of_reg v_3267) (bv_and (bv_xor v_6289 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_6291);
      pure ()
    pat_end;
    pattern fun (v_3261 : Mem) (v_3262 : reg (bv 128)) => do
      v_10193 <- getRegister v_3262;
      v_10195 <- evaluateAddress v_3261;
      v_10196 <- load v_10195 16;
      setRegister (lhs.of_reg v_3262) (bv_and (bv_xor v_10193 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_10196);
      pure ()
    pat_end
