def vpsllq1 : instruction :=
  definst "vpsllq" $ do
    pattern fun (v_3082 : imm int) (v_3080 : reg (bv 128)) (v_3081 : reg (bv 128)) => do
      v_8078 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3082 8 8));
      v_8080 <- getRegister v_3080;
      v_8081 <- eval (extract v_8080 0 64);
      v_8082 <- eval (uvalueMInt v_8078);
      v_8086 <- eval (extract v_8080 64 128);
      setRegister (lhs.of_reg v_3081) (mux (ugt v_8078 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl v_8081 v_8082) 0 (bitwidthMInt v_8081)) (extract (shl v_8086 v_8082) 0 (bitwidthMInt v_8086))));
      pure ()
    pat_end;
    pattern fun (v_3091 : reg (bv 128)) (v_3092 : reg (bv 128)) (v_3093 : reg (bv 128)) => do
      v_8098 <- getRegister v_3091;
      v_8099 <- eval (extract v_8098 64 128);
      v_8101 <- getRegister v_3092;
      v_8102 <- eval (extract v_8101 0 64);
      v_8103 <- eval (uvalueMInt v_8099);
      v_8107 <- eval (extract v_8101 64 128);
      setRegister (lhs.of_reg v_3093) (mux (ugt v_8099 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl v_8102 v_8103) 0 (bitwidthMInt v_8102)) (extract (shl v_8107 v_8103) 0 (bitwidthMInt v_8107))));
      pure ()
    pat_end;
    pattern fun (v_3097 : imm int) (v_3098 : reg (bv 256)) (v_3099 : reg (bv 256)) => do
      v_8115 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3097 8 8));
      v_8117 <- getRegister v_3098;
      v_8118 <- eval (extract v_8117 0 64);
      v_8119 <- eval (uvalueMInt v_8115);
      v_8123 <- eval (extract v_8117 64 128);
      v_8127 <- eval (extract v_8117 128 192);
      v_8131 <- eval (extract v_8117 192 256);
      setRegister (lhs.of_reg v_3099) (mux (ugt v_8115 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl v_8118 v_8119) 0 (bitwidthMInt v_8118)) (concat (extract (shl v_8123 v_8119) 0 (bitwidthMInt v_8123)) (concat (extract (shl v_8127 v_8119) 0 (bitwidthMInt v_8127)) (extract (shl v_8131 v_8119) 0 (bitwidthMInt v_8131))))));
      pure ()
    pat_end;
    pattern fun (v_3108 : reg (bv 128)) (v_3109 : reg (bv 256)) (v_3110 : reg (bv 256)) => do
      v_8145 <- getRegister v_3108;
      v_8146 <- eval (extract v_8145 64 128);
      v_8148 <- getRegister v_3109;
      v_8149 <- eval (extract v_8148 0 64);
      v_8150 <- eval (uvalueMInt v_8146);
      v_8154 <- eval (extract v_8148 64 128);
      v_8158 <- eval (extract v_8148 128 192);
      v_8162 <- eval (extract v_8148 192 256);
      setRegister (lhs.of_reg v_3110) (mux (ugt v_8146 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl v_8149 v_8150) 0 (bitwidthMInt v_8149)) (concat (extract (shl v_8154 v_8150) 0 (bitwidthMInt v_8154)) (concat (extract (shl v_8158 v_8150) 0 (bitwidthMInt v_8158)) (extract (shl v_8162 v_8150) 0 (bitwidthMInt v_8162))))));
      pure ()
    pat_end;
    pattern fun (v_3088 : Mem) (v_3086 : reg (bv 128)) (v_3087 : reg (bv 128)) => do
      v_14989 <- evaluateAddress v_3088;
      v_14990 <- load v_14989 16;
      v_14991 <- eval (extract v_14990 64 128);
      v_14993 <- getRegister v_3086;
      v_14994 <- eval (extract v_14993 0 64);
      v_14995 <- eval (uvalueMInt v_14991);
      v_14999 <- eval (extract v_14993 64 128);
      setRegister (lhs.of_reg v_3087) (mux (ugt v_14991 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl v_14994 v_14995) 0 (bitwidthMInt v_14994)) (extract (shl v_14999 v_14995) 0 (bitwidthMInt v_14999))));
      pure ()
    pat_end;
    pattern fun (v_3103 : Mem) (v_3104 : reg (bv 256)) (v_3105 : reg (bv 256)) => do
      v_15006 <- evaluateAddress v_3103;
      v_15007 <- load v_15006 16;
      v_15008 <- eval (extract v_15007 64 128);
      v_15010 <- getRegister v_3104;
      v_15011 <- eval (extract v_15010 0 64);
      v_15012 <- eval (uvalueMInt v_15008);
      v_15016 <- eval (extract v_15010 64 128);
      v_15020 <- eval (extract v_15010 128 192);
      v_15024 <- eval (extract v_15010 192 256);
      setRegister (lhs.of_reg v_3105) (mux (ugt v_15008 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl v_15011 v_15012) 0 (bitwidthMInt v_15011)) (concat (extract (shl v_15016 v_15012) 0 (bitwidthMInt v_15016)) (concat (extract (shl v_15020 v_15012) 0 (bitwidthMInt v_15020)) (extract (shl v_15024 v_15012) 0 (bitwidthMInt v_15024))))));
      pure ()
    pat_end
