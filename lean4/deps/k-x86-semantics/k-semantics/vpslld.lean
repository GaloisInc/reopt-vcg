def vpslld1 : instruction :=
  definst "vpslld" $ do
    pattern fun (v_3036 : imm int) (v_3034 : reg (bv 128)) (v_3035 : reg (bv 128)) => do
      v_7887 <- eval (handleImmediateWithSignExtend v_3036 8 8);
      v_7890 <- getRegister v_3034;
      v_7891 <- eval (extract v_7890 0 32);
      v_7893 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7887));
      v_7897 <- eval (extract v_7890 32 64);
      v_7901 <- eval (extract v_7890 64 96);
      v_7905 <- eval (extract v_7890 96 128);
      setRegister (lhs.of_reg v_3035) (mux (ugt (concat (expression.bv_nat 56 0) v_7887) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl v_7891 v_7893) 0 (bitwidthMInt v_7891)) (concat (extract (shl v_7897 v_7893) 0 (bitwidthMInt v_7897)) (concat (extract (shl v_7901 v_7893) 0 (bitwidthMInt v_7901)) (extract (shl v_7905 v_7893) 0 (bitwidthMInt v_7905))))));
      pure ()
    pat_end;
    pattern fun (v_3045 : reg (bv 128)) (v_3046 : reg (bv 128)) (v_3047 : reg (bv 128)) => do
      v_7919 <- getRegister v_3045;
      v_7922 <- getRegister v_3046;
      v_7923 <- eval (extract v_7922 0 32);
      v_7925 <- eval (uvalueMInt (extract v_7919 96 128));
      v_7929 <- eval (extract v_7922 32 64);
      v_7933 <- eval (extract v_7922 64 96);
      v_7937 <- eval (extract v_7922 96 128);
      setRegister (lhs.of_reg v_3047) (mux (ugt (extract v_7919 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl v_7923 v_7925) 0 (bitwidthMInt v_7923)) (concat (extract (shl v_7929 v_7925) 0 (bitwidthMInt v_7929)) (concat (extract (shl v_7933 v_7925) 0 (bitwidthMInt v_7933)) (extract (shl v_7937 v_7925) 0 (bitwidthMInt v_7937))))));
      pure ()
    pat_end;
    pattern fun (v_3051 : imm int) (v_3052 : reg (bv 256)) (v_3053 : reg (bv 256)) => do
      v_7946 <- eval (handleImmediateWithSignExtend v_3051 8 8);
      v_7949 <- getRegister v_3052;
      v_7950 <- eval (extract v_7949 0 32);
      v_7952 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7946));
      v_7956 <- eval (extract v_7949 32 64);
      v_7960 <- eval (extract v_7949 64 96);
      v_7964 <- eval (extract v_7949 96 128);
      v_7968 <- eval (extract v_7949 128 160);
      v_7972 <- eval (extract v_7949 160 192);
      v_7976 <- eval (extract v_7949 192 224);
      v_7980 <- eval (extract v_7949 224 256);
      setRegister (lhs.of_reg v_3053) (mux (ugt (concat (expression.bv_nat 56 0) v_7946) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl v_7950 v_7952) 0 (bitwidthMInt v_7950)) (concat (extract (shl v_7956 v_7952) 0 (bitwidthMInt v_7956)) (concat (extract (shl v_7960 v_7952) 0 (bitwidthMInt v_7960)) (concat (extract (shl v_7964 v_7952) 0 (bitwidthMInt v_7964)) (concat (extract (shl v_7968 v_7952) 0 (bitwidthMInt v_7968)) (concat (extract (shl v_7972 v_7952) 0 (bitwidthMInt v_7972)) (concat (extract (shl v_7976 v_7952) 0 (bitwidthMInt v_7976)) (extract (shl v_7980 v_7952) 0 (bitwidthMInt v_7980))))))))));
      pure ()
    pat_end;
    pattern fun (v_3062 : reg (bv 128)) (v_3063 : reg (bv 256)) (v_3064 : reg (bv 256)) => do
      v_7998 <- getRegister v_3062;
      v_8001 <- getRegister v_3063;
      v_8002 <- eval (extract v_8001 0 32);
      v_8004 <- eval (uvalueMInt (extract v_7998 96 128));
      v_8008 <- eval (extract v_8001 32 64);
      v_8012 <- eval (extract v_8001 64 96);
      v_8016 <- eval (extract v_8001 96 128);
      v_8020 <- eval (extract v_8001 128 160);
      v_8024 <- eval (extract v_8001 160 192);
      v_8028 <- eval (extract v_8001 192 224);
      v_8032 <- eval (extract v_8001 224 256);
      setRegister (lhs.of_reg v_3064) (mux (ugt (extract v_7998 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl v_8002 v_8004) 0 (bitwidthMInt v_8002)) (concat (extract (shl v_8008 v_8004) 0 (bitwidthMInt v_8008)) (concat (extract (shl v_8012 v_8004) 0 (bitwidthMInt v_8012)) (concat (extract (shl v_8016 v_8004) 0 (bitwidthMInt v_8016)) (concat (extract (shl v_8020 v_8004) 0 (bitwidthMInt v_8020)) (concat (extract (shl v_8024 v_8004) 0 (bitwidthMInt v_8024)) (concat (extract (shl v_8028 v_8004) 0 (bitwidthMInt v_8028)) (extract (shl v_8032 v_8004) 0 (bitwidthMInt v_8032))))))))));
      pure ()
    pat_end;
    pattern fun (v_3042 : Mem) (v_3040 : reg (bv 128)) (v_3041 : reg (bv 128)) => do
      v_14913 <- evaluateAddress v_3042;
      v_14914 <- load v_14913 16;
      v_14917 <- getRegister v_3040;
      v_14918 <- eval (extract v_14917 0 32);
      v_14920 <- eval (uvalueMInt (extract v_14914 96 128));
      v_14924 <- eval (extract v_14917 32 64);
      v_14928 <- eval (extract v_14917 64 96);
      v_14932 <- eval (extract v_14917 96 128);
      setRegister (lhs.of_reg v_3041) (mux (ugt (extract v_14914 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl v_14918 v_14920) 0 (bitwidthMInt v_14918)) (concat (extract (shl v_14924 v_14920) 0 (bitwidthMInt v_14924)) (concat (extract (shl v_14928 v_14920) 0 (bitwidthMInt v_14928)) (extract (shl v_14932 v_14920) 0 (bitwidthMInt v_14932))))));
      pure ()
    pat_end;
    pattern fun (v_3057 : Mem) (v_3058 : reg (bv 256)) (v_3059 : reg (bv 256)) => do
      v_14941 <- evaluateAddress v_3057;
      v_14942 <- load v_14941 16;
      v_14945 <- getRegister v_3058;
      v_14946 <- eval (extract v_14945 0 32);
      v_14948 <- eval (uvalueMInt (extract v_14942 96 128));
      v_14952 <- eval (extract v_14945 32 64);
      v_14956 <- eval (extract v_14945 64 96);
      v_14960 <- eval (extract v_14945 96 128);
      v_14964 <- eval (extract v_14945 128 160);
      v_14968 <- eval (extract v_14945 160 192);
      v_14972 <- eval (extract v_14945 192 224);
      v_14976 <- eval (extract v_14945 224 256);
      setRegister (lhs.of_reg v_3059) (mux (ugt (extract v_14942 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl v_14946 v_14948) 0 (bitwidthMInt v_14946)) (concat (extract (shl v_14952 v_14948) 0 (bitwidthMInt v_14952)) (concat (extract (shl v_14956 v_14948) 0 (bitwidthMInt v_14956)) (concat (extract (shl v_14960 v_14948) 0 (bitwidthMInt v_14960)) (concat (extract (shl v_14964 v_14948) 0 (bitwidthMInt v_14964)) (concat (extract (shl v_14968 v_14948) 0 (bitwidthMInt v_14968)) (concat (extract (shl v_14972 v_14948) 0 (bitwidthMInt v_14972)) (extract (shl v_14976 v_14948) 0 (bitwidthMInt v_14976))))))))));
      pure ()
    pat_end
