def rorxl1 : instruction :=
  definst "rorxl" $ do
    pattern fun (v_2775 : imm int) (v_2778 : reg (bv 32)) (v_2779 : reg (bv 32)) => do
      v_5714 <- getRegister v_2778;
      v_5717 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2775 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2779) (bv_or (lshr v_5714 (uvalueMInt v_5717)) (extract (shl v_5714 (uvalueMInt (sub (expression.bv_nat 32 32) v_5717))) 0 (bitwidthMInt v_5714)));
      pure ()
    pat_end;
    pattern fun (v_2765 : imm int) (v_2766 : Mem) (v_2769 : reg (bv 32)) => do
      v_12923 <- evaluateAddress v_2766;
      v_12924 <- load v_12923 4;
      v_12927 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2765 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2769) (bv_or (lshr v_12924 (uvalueMInt v_12927)) (extract (shl v_12924 (uvalueMInt (sub (expression.bv_nat 32 32) v_12927))) 0 (bitwidthMInt v_12924)));
      pure ()
    pat_end
