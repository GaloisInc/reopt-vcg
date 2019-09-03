def vpextrw1 : instruction :=
  definst "vpextrw" $ do
    pattern fun (v_3146 : imm int) (v_3143 : reg (bv 128)) (v_3148 : reg (bv 32)) => do
      v_8781 <- getRegister v_3143;
      setRegister (lhs.of_reg v_3148) (concat (expression.bv_nat 16 0) (extract (lshr v_8781 (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3146 8 8) 5 8)) 4) 0 128))) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3152 : imm int) (v_3149 : reg (bv 128)) (v_3153 : reg (bv 64)) => do
      v_8792 <- getRegister v_3149;
      setRegister (lhs.of_reg v_3153) (concat (expression.bv_nat 48 0) (extract (lshr v_8792 (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3152 8 8) 5 8)) 4) 0 128))) 112 128));
      pure ()
    pat_end;
    pattern fun (v_3142 : imm int) (v_3138 : reg (bv 128)) (v_3141 : Mem) => do
      v_19668 <- evaluateAddress v_3141;
      v_19669 <- getRegister v_3138;
      store v_19668 (extract (lshr v_19669 (uvalueMInt (extract (shl (concat (expression.bv_nat 125 0) (extract (handleImmediateWithSignExtend v_3142 8 8) 5 8)) 4) 0 128))) 112 128) 2;
      pure ()
    pat_end
