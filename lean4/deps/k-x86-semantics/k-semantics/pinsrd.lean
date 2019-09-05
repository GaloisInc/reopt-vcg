def pinsrd1 : instruction :=
  definst "pinsrd" $ do
    pattern fun (v_2568 : imm int) (v_2567 : reg (bv 32)) (v_2566 : reg (bv 128)) => do
      v_4460 <- getRegister v_2566;
      v_4465 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2568 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_4466 <- eval (shl (expression.bv_nat 128 4294967295) v_4465);
      v_4470 <- getRegister v_2567;
      setRegister (lhs.of_reg v_2566) (bv_or (bv_and v_4460 (bv_xor (extract v_4466 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_4470) v_4465) v_4466) 0 128));
      pure ()
    pat_end;
    pattern fun (v_2562 : imm int) (v_2563 : Mem) (v_2561 : reg (bv 128)) => do
      v_11394 <- getRegister v_2561;
      v_11399 <- eval (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2562 8 8) 6 8)) (expression.bv_nat 128 5)) 0 128);
      v_11400 <- eval (shl (expression.bv_nat 128 4294967295) v_11399);
      v_11404 <- evaluateAddress v_2563;
      v_11405 <- load v_11404 4;
      setRegister (lhs.of_reg v_2561) (bv_or (bv_and v_11394 (bv_xor (extract v_11400 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_11405) v_11399) v_11400) 0 128));
      pure ()
    pat_end
