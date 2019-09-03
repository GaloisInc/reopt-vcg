def rorxq1 : instruction :=
  definst "rorxq" $ do
    pattern fun (v_2809 : imm int) (v_2811 : reg (bv 64)) (v_2812 : reg (bv 64)) => do
      v_5756 <- getRegister v_2811;
      v_5759 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2809 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2812) (bv_or (lshr v_5756 (uvalueMInt v_5759)) (extract (shl v_5756 (uvalueMInt (sub (expression.bv_nat 64 64) v_5759))) 0 64));
      pure ()
    pat_end;
    pattern fun (v_2800 : imm int) (v_2799 : Mem) (v_2801 : reg (bv 64)) => do
      v_12863 <- evaluateAddress v_2799;
      v_12864 <- load v_12863 8;
      v_12867 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2800 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2801) (bv_or (lshr v_12864 (uvalueMInt v_12867)) (extract (shl v_12864 (uvalueMInt (sub (expression.bv_nat 64 64) v_12867))) 0 64));
      pure ()
    pat_end
