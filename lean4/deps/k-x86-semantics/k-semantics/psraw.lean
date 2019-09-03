def psraw1 : instruction :=
  definst "psraw" $ do
    pattern fun (v_3017 : imm int) (v_3016 : reg (bv 128)) => do
      v_8016 <- getRegister v_3016;
      v_8017 <- eval (extract v_8016 0 16);
      v_8021 <- eval (handleImmediateWithSignExtend v_3017 8 8);
      v_8026 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8021) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8021)));
      v_8028 <- eval (extract v_8016 16 32);
      v_8033 <- eval (extract v_8016 32 48);
      v_8038 <- eval (extract v_8016 48 64);
      v_8043 <- eval (extract v_8016 64 80);
      v_8048 <- eval (extract v_8016 80 96);
      v_8053 <- eval (extract v_8016 96 112);
      v_8058 <- eval (extract v_8016 112 128);
      setRegister (lhs.of_reg v_3016) (concat (ashr (mi (bitwidthMInt v_8017) (svalueMInt v_8017)) v_8026) (concat (ashr (mi (bitwidthMInt v_8028) (svalueMInt v_8028)) v_8026) (concat (ashr (mi (bitwidthMInt v_8033) (svalueMInt v_8033)) v_8026) (concat (ashr (mi (bitwidthMInt v_8038) (svalueMInt v_8038)) v_8026) (concat (ashr (mi (bitwidthMInt v_8043) (svalueMInt v_8043)) v_8026) (concat (ashr (mi (bitwidthMInt v_8048) (svalueMInt v_8048)) v_8026) (concat (ashr (mi (bitwidthMInt v_8053) (svalueMInt v_8053)) v_8026) (ashr (mi (bitwidthMInt v_8058) (svalueMInt v_8058)) v_8026))))))));
      pure ()
    pat_end;
    pattern fun (v_3025 : reg (bv 128)) (v_3026 : reg (bv 128)) => do
      v_8075 <- getRegister v_3026;
      v_8076 <- eval (extract v_8075 0 16);
      v_8080 <- getRegister v_3025;
      v_8085 <- eval (uvalueMInt (mux (ugt (extract v_8080 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8080 112 128)));
      v_8087 <- eval (extract v_8075 16 32);
      v_8092 <- eval (extract v_8075 32 48);
      v_8097 <- eval (extract v_8075 48 64);
      v_8102 <- eval (extract v_8075 64 80);
      v_8107 <- eval (extract v_8075 80 96);
      v_8112 <- eval (extract v_8075 96 112);
      v_8117 <- eval (extract v_8075 112 128);
      setRegister (lhs.of_reg v_3026) (concat (ashr (mi (bitwidthMInt v_8076) (svalueMInt v_8076)) v_8085) (concat (ashr (mi (bitwidthMInt v_8087) (svalueMInt v_8087)) v_8085) (concat (ashr (mi (bitwidthMInt v_8092) (svalueMInt v_8092)) v_8085) (concat (ashr (mi (bitwidthMInt v_8097) (svalueMInt v_8097)) v_8085) (concat (ashr (mi (bitwidthMInt v_8102) (svalueMInt v_8102)) v_8085) (concat (ashr (mi (bitwidthMInt v_8107) (svalueMInt v_8107)) v_8085) (concat (ashr (mi (bitwidthMInt v_8112) (svalueMInt v_8112)) v_8085) (ashr (mi (bitwidthMInt v_8117) (svalueMInt v_8117)) v_8085))))))));
      pure ()
    pat_end;
    pattern fun (v_3020 : Mem) (v_3021 : reg (bv 128)) => do
      v_15077 <- getRegister v_3021;
      v_15078 <- eval (extract v_15077 0 16);
      v_15082 <- evaluateAddress v_3020;
      v_15083 <- load v_15082 16;
      v_15088 <- eval (uvalueMInt (mux (ugt (extract v_15083 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_15083 112 128)));
      v_15090 <- eval (extract v_15077 16 32);
      v_15095 <- eval (extract v_15077 32 48);
      v_15100 <- eval (extract v_15077 48 64);
      v_15105 <- eval (extract v_15077 64 80);
      v_15110 <- eval (extract v_15077 80 96);
      v_15115 <- eval (extract v_15077 96 112);
      v_15120 <- eval (extract v_15077 112 128);
      setRegister (lhs.of_reg v_3021) (concat (ashr (mi (bitwidthMInt v_15078) (svalueMInt v_15078)) v_15088) (concat (ashr (mi (bitwidthMInt v_15090) (svalueMInt v_15090)) v_15088) (concat (ashr (mi (bitwidthMInt v_15095) (svalueMInt v_15095)) v_15088) (concat (ashr (mi (bitwidthMInt v_15100) (svalueMInt v_15100)) v_15088) (concat (ashr (mi (bitwidthMInt v_15105) (svalueMInt v_15105)) v_15088) (concat (ashr (mi (bitwidthMInt v_15110) (svalueMInt v_15110)) v_15088) (concat (ashr (mi (bitwidthMInt v_15115) (svalueMInt v_15115)) v_15088) (ashr (mi (bitwidthMInt v_15120) (svalueMInt v_15120)) v_15088))))))));
      pure ()
    pat_end
