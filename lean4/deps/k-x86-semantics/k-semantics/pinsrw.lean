def pinsrw1 : instruction :=
  definst "pinsrw" $ do
    pattern fun (v_2521 : imm int) (v_2522 : reg (bv 32)) (v_2520 : reg (bv 128)) => do
      v_4482 <- getRegister v_2520;
      v_4485 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2521 8 8) 5 8));
      v_4489 <- eval (uvalueMInt (extract (shl v_4485 4) 0 (bitwidthMInt v_4485)));
      v_4491 <- eval (extract (shl (expression.bv_nat 128 65535) v_4489) 0 128);
      v_4496 <- getRegister v_2522;
      v_4497 <- eval (concat (expression.bv_nat 96 0) v_4496);
      setRegister (lhs.of_reg v_2520) (bv_or (bv_and v_4482 (bv_xor v_4491 (mi (bitwidthMInt v_4491) -1))) (bv_and (extract (shl v_4497 v_4489) 0 (bitwidthMInt v_4497)) v_4491));
      pure ()
    pat_end;
    pattern fun (v_2516 : imm int) (v_2514 : Mem) (v_2515 : reg (bv 128)) => do
      v_11894 <- getRegister v_2515;
      v_11897 <- eval (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_2516 8 8) 5 8));
      v_11901 <- eval (uvalueMInt (extract (shl v_11897 4) 0 (bitwidthMInt v_11897)));
      v_11903 <- eval (extract (shl (expression.bv_nat 128 65535) v_11901) 0 128);
      v_11908 <- evaluateAddress v_2514;
      v_11909 <- load v_11908 2;
      v_11910 <- eval (concat (expression.bv_nat 112 0) v_11909);
      setRegister (lhs.of_reg v_2515) (bv_or (bv_and v_11894 (bv_xor v_11903 (mi (bitwidthMInt v_11903) -1))) (bv_and (extract (shl v_11910 v_11901) 0 (bitwidthMInt v_11910)) v_11903));
      pure ()
    pat_end
