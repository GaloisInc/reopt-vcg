def dpps1 : instruction :=
  definst "dpps" $ do
    pattern fun (v_2878 : imm int) (v_2879 : reg (bv 128)) (v_2880 : reg (bv 128)) => do
      v_4702 <- eval (handleImmediateWithSignExtend v_2878 8 8);
      v_4705 <- getRegister v_2880;
      v_4708 <- getRegister v_2879;
      v_4749 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4702 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4705 96 128) 24 8) (MInt2Float (extract v_4708 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4702 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4705 64 96) 24 8) (MInt2Float (extract v_4708 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_4702 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4705 32 64) 24 8) (MInt2Float (extract v_4708 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_4702 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4705 0 32) 24 8) (MInt2Float (extract v_4708 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2880) (concat (concat (concat (mux (isBitSet v_4702 4) v_4749 (expression.bv_nat 32 0)) (mux (isBitSet v_4702 5) v_4749 (expression.bv_nat 32 0))) (mux (isBitSet v_4702 6) v_4749 (expression.bv_nat 32 0))) (mux (isBitSet v_4702 7) v_4749 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2873 : imm int) (v_2874 : Mem) (v_2875 : reg (bv 128)) => do
      v_8198 <- eval (handleImmediateWithSignExtend v_2873 8 8);
      v_8201 <- getRegister v_2875;
      v_8204 <- evaluateAddress v_2874;
      v_8205 <- load v_8204 16;
      v_8246 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_8198 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8201 96 128) 24 8) (MInt2Float (extract v_8205 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_8198 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8201 64 96) 24 8) (MInt2Float (extract v_8205 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_8198 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8201 32 64) 24 8) (MInt2Float (extract v_8205 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_8198 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8201 0 32) 24 8) (MInt2Float (extract v_8205 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2875) (concat (concat (concat (mux (isBitSet v_8198 4) v_8246 (expression.bv_nat 32 0)) (mux (isBitSet v_8198 5) v_8246 (expression.bv_nat 32 0))) (mux (isBitSet v_8198 6) v_8246 (expression.bv_nat 32 0))) (mux (isBitSet v_8198 7) v_8246 (expression.bv_nat 32 0)));
      pure ()
    pat_end
