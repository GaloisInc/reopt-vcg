def psrad1 : instruction :=
  definst "psrad" $ do
    pattern fun (v_3003 : imm int) (v_3002 : reg (bv 128)) => do
      v_7950 <- getRegister v_3002;
      v_7951 <- eval (extract v_7950 0 32);
      v_7955 <- eval (handleImmediateWithSignExtend v_3003 8 8);
      v_7960 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_7955) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_7955)));
      v_7962 <- eval (extract v_7950 32 64);
      v_7967 <- eval (extract v_7950 64 96);
      v_7972 <- eval (extract v_7950 96 128);
      setRegister (lhs.of_reg v_3002) (concat (ashr (mi (bitwidthMInt v_7951) (svalueMInt v_7951)) v_7960) (concat (ashr (mi (bitwidthMInt v_7962) (svalueMInt v_7962)) v_7960) (concat (ashr (mi (bitwidthMInt v_7967) (svalueMInt v_7967)) v_7960) (ashr (mi (bitwidthMInt v_7972) (svalueMInt v_7972)) v_7960))));
      pure ()
    pat_end;
    pattern fun (v_3011 : reg (bv 128)) (v_3012 : reg (bv 128)) => do
      v_7985 <- getRegister v_3012;
      v_7986 <- eval (extract v_7985 0 32);
      v_7990 <- getRegister v_3011;
      v_7995 <- eval (uvalueMInt (mux (ugt (extract v_7990 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_7990 96 128)));
      v_7997 <- eval (extract v_7985 32 64);
      v_8002 <- eval (extract v_7985 64 96);
      v_8007 <- eval (extract v_7985 96 128);
      setRegister (lhs.of_reg v_3012) (concat (ashr (mi (bitwidthMInt v_7986) (svalueMInt v_7986)) v_7995) (concat (ashr (mi (bitwidthMInt v_7997) (svalueMInt v_7997)) v_7995) (concat (ashr (mi (bitwidthMInt v_8002) (svalueMInt v_8002)) v_7995) (ashr (mi (bitwidthMInt v_8007) (svalueMInt v_8007)) v_7995))));
      pure ()
    pat_end;
    pattern fun (v_3006 : Mem) (v_3007 : reg (bv 128)) => do
      v_15045 <- getRegister v_3007;
      v_15046 <- eval (extract v_15045 0 32);
      v_15050 <- evaluateAddress v_3006;
      v_15051 <- load v_15050 16;
      v_15056 <- eval (uvalueMInt (mux (ugt (extract v_15051 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_15051 96 128)));
      v_15058 <- eval (extract v_15045 32 64);
      v_15063 <- eval (extract v_15045 64 96);
      v_15068 <- eval (extract v_15045 96 128);
      setRegister (lhs.of_reg v_3007) (concat (ashr (mi (bitwidthMInt v_15046) (svalueMInt v_15046)) v_15056) (concat (ashr (mi (bitwidthMInt v_15058) (svalueMInt v_15058)) v_15056) (concat (ashr (mi (bitwidthMInt v_15063) (svalueMInt v_15063)) v_15056) (ashr (mi (bitwidthMInt v_15068) (svalueMInt v_15068)) v_15056))));
      pure ()
    pat_end
