def vinsertf1281 : instruction :=
  definst "vinsertf128" $ do
    pattern fun (v_2452 : imm int) (v_2454 : reg (bv 128)) (v_2455 : reg (bv 256)) (v_2456 : reg (bv 256)) => do
      v_4187 <- getRegister v_2455;
      v_4189 <- getRegister v_2454;
      setRegister (lhs.of_reg v_2456) (mux (eq (extract (handleImmediateWithSignExtend v_2452 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_4187 0 128) v_4189) (concat v_4189 (extract v_4187 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2446 : imm int) (v_2447 : Mem) (v_2448 : reg (bv 256)) (v_2449 : reg (bv 256)) => do
      v_9808 <- getRegister v_2448;
      v_9810 <- evaluateAddress v_2447;
      v_9811 <- load v_9810 16;
      setRegister (lhs.of_reg v_2449) (mux (eq (extract (handleImmediateWithSignExtend v_2446 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_9808 0 128) v_9811) (concat v_9811 (extract v_9808 128 256)));
      pure ()
    pat_end
