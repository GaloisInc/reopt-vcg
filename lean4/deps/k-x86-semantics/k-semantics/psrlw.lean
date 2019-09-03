def psrlw1 : instruction :=
  definst "psrlw" $ do
    pattern fun (v_3064 : imm int) (v_3063 : reg (bv 128)) => do
      v_8211 <- eval (handleImmediateWithSignExtend v_3064 8 8);
      v_8214 <- getRegister v_3063;
      v_8217 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_8211));
      setRegister (lhs.of_reg v_3063) (mux (ugt (concat (expression.bv_nat 56 0) v_8211) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_8214 0 16) v_8217) (concat (lshr (extract v_8214 16 32) v_8217) (concat (lshr (extract v_8214 32 48) v_8217) (concat (lshr (extract v_8214 48 64) v_8217) (concat (lshr (extract v_8214 64 80) v_8217) (concat (lshr (extract v_8214 80 96) v_8217) (concat (lshr (extract v_8214 96 112) v_8217) (lshr (extract v_8214 112 128) v_8217)))))))));
      pure ()
    pat_end;
    pattern fun (v_3072 : reg (bv 128)) (v_3073 : reg (bv 128)) => do
      v_8246 <- getRegister v_3072;
      v_8249 <- getRegister v_3073;
      v_8252 <- eval (uvalueMInt (extract v_8246 112 128));
      setRegister (lhs.of_reg v_3073) (mux (ugt (extract v_8246 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_8249 0 16) v_8252) (concat (lshr (extract v_8249 16 32) v_8252) (concat (lshr (extract v_8249 32 48) v_8252) (concat (lshr (extract v_8249 48 64) v_8252) (concat (lshr (extract v_8249 64 80) v_8252) (concat (lshr (extract v_8249 80 96) v_8252) (concat (lshr (extract v_8249 96 112) v_8252) (lshr (extract v_8249 112 128) v_8252)))))))));
      pure ()
    pat_end;
    pattern fun (v_3067 : Mem) (v_3068 : reg (bv 128)) => do
      v_15166 <- evaluateAddress v_3067;
      v_15167 <- load v_15166 16;
      v_15170 <- getRegister v_3068;
      v_15173 <- eval (uvalueMInt (extract v_15167 112 128));
      setRegister (lhs.of_reg v_3068) (mux (ugt (extract v_15167 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_15170 0 16) v_15173) (concat (lshr (extract v_15170 16 32) v_15173) (concat (lshr (extract v_15170 32 48) v_15173) (concat (lshr (extract v_15170 48 64) v_15173) (concat (lshr (extract v_15170 64 80) v_15173) (concat (lshr (extract v_15170 80 96) v_15173) (concat (lshr (extract v_15170 96 112) v_15173) (lshr (extract v_15170 112 128) v_15173)))))))));
      pure ()
    pat_end
