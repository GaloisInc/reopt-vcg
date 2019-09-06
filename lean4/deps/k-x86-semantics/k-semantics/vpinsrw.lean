def vpinsrw1 : instruction :=
  definst "vpinsrw" $ do
    pattern fun (v_3421 : imm int) (v_3424 : reg (bv 32)) (v_3422 : reg (bv 128)) (v_3423 : reg (bv 128)) => do
      v_9696 <- getRegister v_3422;
      v_9701 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3421 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_9702 <- eval (shl (expression.bv_nat 128 65535) v_9701);
      v_9706 <- getRegister v_3424;
      setRegister (lhs.of_reg v_3423) (bv_or (bv_and v_9696 (bv_xor (extract v_9702 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 96 0) v_9706) v_9701) v_9702) 0 128));
      pure ()
    pat_end;
    pattern fun (v_3416 : imm int) (v_3415 : Mem) (v_3417 : reg (bv 128)) (v_3418 : reg (bv 128)) => do
      v_18049 <- getRegister v_3417;
      v_18054 <- eval (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3416 8 8) 5 8)) (expression.bv_nat 128 4)) 0 128);
      v_18055 <- eval (shl (expression.bv_nat 128 65535) v_18054);
      v_18059 <- evaluateAddress v_3415;
      v_18060 <- load v_18059 2;
      setRegister (lhs.of_reg v_3418) (bv_or (bv_and v_18049 (bv_xor (extract v_18055 0 128) (expression.bv_nat 128 340282366920938463463374607431768211455))) (extract (bv_and (shl (concat (expression.bv_nat 112 0) v_18060) v_18054) v_18055) 0 128));
      pure ()
    pat_end
