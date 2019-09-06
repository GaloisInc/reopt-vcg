def pandn1 : instruction :=
  definst "pandn" $ do
    pattern fun (v_3291 : reg (bv 128)) (v_3292 : reg (bv 128)) => do
      v_6316 <- getRegister v_3292;
      v_6318 <- getRegister v_3291;
      setRegister (lhs.of_reg v_3292) (bv_and (bv_xor v_6316 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_6318);
      pure ()
    pat_end;
    pattern fun (v_3287 : Mem) (v_3288 : reg (bv 128)) => do
      v_10220 <- getRegister v_3288;
      v_10222 <- evaluateAddress v_3287;
      v_10223 <- load v_10222 16;
      setRegister (lhs.of_reg v_3288) (bv_and (bv_xor v_10220 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_10223);
      pure ()
    pat_end
