def rorxl1 : instruction :=
  definst "rorxl" $ do
    pattern fun (v_2788 : imm int) (v_2790 : reg (bv 32)) (v_2791 : reg (bv 32)) => do
      v_5734 <- getRegister v_2790;
      v_5737 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2788 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2791) (bv_or (lshr v_5734 (uvalueMInt v_5737)) (extract (shl v_5734 (uvalueMInt (sub (expression.bv_nat 32 32) v_5737))) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2779 : imm int) (v_2778 : Mem) (v_2780 : reg (bv 32)) => do
      v_12849 <- evaluateAddress v_2778;
      v_12850 <- load v_12849 4;
      v_12853 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2779 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2780) (bv_or (lshr v_12850 (uvalueMInt v_12853)) (extract (shl v_12850 (uvalueMInt (sub (expression.bv_nat 32 32) v_12853))) 0 32));
      pure ()
    pat_end
