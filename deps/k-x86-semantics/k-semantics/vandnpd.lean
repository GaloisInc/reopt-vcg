def vandnpd : instruction :=
  definst "vandnpd" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      setRegister (lhs.of_reg xmm_2) (bv_and (bv_xor v_3 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_5);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 32;
      setRegister (lhs.of_reg ymm_2) (bv_and (bv_xor v_3 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_5);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (bv_and (bv_xor v_3 (expression.bv_nat 128 340282366920938463463374607431768211455)) v_4);
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let v_4 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg ymm_2) (bv_and (bv_xor v_3 (expression.bv_nat 256 115792089237316195423570985008687907853269984665640564039457584007913129639935)) v_4);
      pure ()
     action
