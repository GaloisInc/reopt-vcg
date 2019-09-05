def pinsrw1 : instruction :=
  definst "pinsrw" $ do
    pattern fun (v_2585 : imm int) (v_2584 : reg (bv 32)) (v_2583 : reg (bv 128)) => do
      v_4499 <- getRegister v_2583;
      v_4504 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2585 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_4505 <- eval (shl (expression.bv_nat 128 65535) v_4504);
      v_4509 <- getRegister v_2584;
      setRegister (lhs.of_reg v_2583) (bv_or (bv_and v_4499 (bv_xor (extract v_4505 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_4509) v_4504) v_4505) 0 128));
      pure ()
    pat_end;
    pattern fun (v_2579 : imm int) (v_2580 : Mem) (v_2578 : reg (bv 128)) => do
      v_11412 <- getRegister v_2578;
      v_11417 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2579 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_11418 <- eval (shl (expression.bv_nat 128 65535) v_11417);
      v_11422 <- evaluateAddress v_2580;
      v_11423 <- load v_11422 2;
      setRegister (lhs.of_reg v_2578) (bv_or (bv_and v_11412 (bv_xor (extract v_11418 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 112 0) v_11423) v_11417) v_11418) 0 128));
      pure ()
    pat_end
