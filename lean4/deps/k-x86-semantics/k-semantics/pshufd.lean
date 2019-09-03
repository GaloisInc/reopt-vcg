def pshufd1 : instruction :=
  definst "pshufd" $ do
    pattern fun (v_2914 : imm int) (v_2915 : reg (bv 128)) (v_2916 : reg (bv 128)) => do
      v_7142 <- getRegister v_2915;
      v_7143 <- eval (handleImmediateWithSignExtend v_2914 8 8);
      setRegister (lhs.of_reg v_2916) (concat (extract (lshr v_7142 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7143 0 2)) 5) 0 128))) 96 128) (concat (extract (lshr v_7142 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7143 2 4)) 5) 0 128))) 96 128) (concat (extract (lshr v_7142 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7143 4 6)) 5) 0 128))) 96 128) (extract (lshr v_7142 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_7143 6 8)) 5) 0 128))) 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2910 : imm int) (v_2909 : Mem) (v_2911 : reg (bv 128)) => do
      v_14039 <- evaluateAddress v_2909;
      v_14040 <- load v_14039 16;
      v_14041 <- eval (handleImmediateWithSignExtend v_2910 8 8);
      setRegister (lhs.of_reg v_2911) (concat (extract (lshr v_14040 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14041 0 2)) 5) 0 128))) 96 128) (concat (extract (lshr v_14040 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14041 2 4)) 5) 0 128))) 96 128) (concat (extract (lshr v_14040 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14041 4 6)) 5) 0 128))) 96 128) (extract (lshr v_14040 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract v_14041 6 8)) 5) 0 128))) 96 128))));
      pure ()
    pat_end
