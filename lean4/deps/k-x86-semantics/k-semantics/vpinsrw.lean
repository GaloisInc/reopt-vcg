def vpinsrw1 : instruction :=
  definst "vpinsrw" $ do
    pattern fun (v_3345 : imm int) (v_3347 : reg (bv 32)) (v_3341 : reg (bv 128)) (v_3342 : reg (bv 128)) => do
      v_9817 <- getRegister v_3341;
      v_9823 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3345 8 8) 5 8)) 4) 0 128));
      v_9825 <- eval (extract (shl (expression.bv_nat 128 65535) v_9823) 0 128);
      v_9828 <- getRegister v_3347;
      setRegister (lhs.of_reg v_3342) (bv_or (bv_and v_9817 (bv_xor v_9825 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 96 0) v_9828) v_9823) 0 128) v_9825));
      pure ()
    pat_end;
    pattern fun (v_3340 : imm int) (v_3339 : Mem) (v_3335 : reg (bv 128)) (v_3336 : reg (bv 128)) => do
      v_18412 <- getRegister v_3335;
      v_18418 <- eval (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3340 8 8) 5 8)) 4) 0 128));
      v_18420 <- eval (extract (shl (expression.bv_nat 128 65535) v_18418) 0 128);
      v_18423 <- evaluateAddress v_3339;
      v_18424 <- load v_18423 2;
      setRegister (lhs.of_reg v_3336) (bv_or (bv_and v_18412 (bv_xor v_18420 (expression.bv_nat 128 340282366920938463463374607431768211455))) (bv_and (extract (shl (concat (expression.bv_nat 112 0) v_18424) v_18418) 0 128) v_18420));
      pure ()
    pat_end
