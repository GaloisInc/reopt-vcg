def rorxq1 : instruction :=
  definst "rorxq" $ do
    pattern fun (v_2796 : imm int) (v_2800 : reg (bv 64)) (v_2801 : reg (bv 64)) => do
      v_5737 <- getRegister v_2800;
      v_5740 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2796 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2801) (bv_or (lshr v_5737 (uvalueMInt v_5740)) (extract (shl v_5737 (uvalueMInt (sub (expression.bv_nat 64 64) v_5740))) 0 (bitwidthMInt v_5737)));
      pure ()
    pat_end;
    pattern fun (v_2786 : imm int) (v_2787 : Mem) (v_2790 : reg (bv 64)) => do
      v_12938 <- evaluateAddress v_2787;
      v_12939 <- load v_12938 8;
      v_12942 <- eval (bv_and (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2786 8 8)) (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_2790) (bv_or (lshr v_12939 (uvalueMInt v_12942)) (extract (shl v_12939 (uvalueMInt (sub (expression.bv_nat 64 64) v_12942))) 0 (bitwidthMInt v_12939)));
      pure ()
    pat_end
