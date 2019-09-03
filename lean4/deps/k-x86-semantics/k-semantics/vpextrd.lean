def vpextrd1 : instruction :=
  definst "vpextrd" $ do
    pattern fun (v_3124 : imm int) (v_3121 : reg (bv 128)) (v_3126 : reg (bv 32)) => do
      v_8751 <- getRegister v_3121;
      setRegister (lhs.of_reg v_3126) (extract (lshr v_8751 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3124 8 8) 6 8)) 5) 0 128))) 96 128);
      pure ()
    pat_end;
    pattern fun (v_3120 : imm int) (v_3116 : reg (bv 128)) (v_3119 : Mem) => do
      v_19646 <- evaluateAddress v_3119;
      v_19647 <- getRegister v_3116;
      store v_19646 (extract (lshr v_19647 (uvalueMInt (extract (shl (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_3120 8 8) 6 8)) 5) 0 128))) 96 128) 4;
      pure ()
    pat_end
