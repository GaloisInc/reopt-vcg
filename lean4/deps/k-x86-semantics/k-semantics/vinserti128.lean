def vinserti1281 : instruction :=
  definst "vinserti128" $ do
    pattern fun (v_2465 : imm int) (v_2467 : reg (bv 128)) (v_2468 : reg (bv 256)) (v_2469 : reg (bv 256)) => do
      v_4204 <- getRegister v_2468;
      v_4206 <- getRegister v_2467;
      setRegister (lhs.of_reg v_2469) (mux (eq (extract (handleImmediateWithSignExtend v_2465 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_4204 0 128) v_4206) (concat v_4206 (extract v_4204 128 256)));
      pure ()
    pat_end;
    pattern fun (v_2459 : imm int) (v_2460 : Mem) (v_2461 : reg (bv 256)) (v_2462 : reg (bv 256)) => do
      v_9820 <- getRegister v_2461;
      v_9822 <- evaluateAddress v_2460;
      v_9823 <- load v_9822 16;
      setRegister (lhs.of_reg v_2462) (mux (eq (extract (handleImmediateWithSignExtend v_2459 8 8) 7 8) (expression.bv_nat 1 0)) (concat (extract v_9820 0 128) v_9823) (concat v_9823 (extract v_9820 128 256)));
      pure ()
    pat_end
