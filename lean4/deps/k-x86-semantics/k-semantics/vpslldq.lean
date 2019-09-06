def vpslldq1 : instruction :=
  definst "vpslldq" $ do
    pattern fun (v_3159 : imm int) (v_3161 : reg (bv 128)) (v_3162 : reg (bv 128)) => do
      v_7806 <- getRegister v_3161;
      v_7807 <- eval (handleImmediateWithSignExtend v_3159 8 8);
      setRegister (lhs.of_reg v_3162) (extract (shl v_7806 (extract (shl (mux (ugt v_7807 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7807)) (expression.bv_nat 128 3)) 0 128)) 0 128);
      pure ()
    pat_end;
    pattern fun (v_3165 : imm int) (v_3167 : reg (bv 256)) (v_3168 : reg (bv 256)) => do
      v_7816 <- getRegister v_3167;
      v_7818 <- eval (handleImmediateWithSignExtend v_3165 8 8);
      v_7823 <- eval (extract (shl (mux (ugt v_7818 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) (concat (expression.bv_nat 120 0) v_7818)) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg v_3168) (concat (extract (shl (extract v_7816 0 128) v_7823) 0 128) (extract (shl (extract v_7816 128 256) v_7823) 0 128));
      pure ()
    pat_end
