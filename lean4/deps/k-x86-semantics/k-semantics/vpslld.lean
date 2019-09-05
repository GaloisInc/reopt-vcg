def vpslld1 : instruction :=
  definst "vpslld" $ do
    pattern fun (v_3096 : imm int) (v_3100 : reg (bv 128)) (v_3101 : reg (bv 128)) => do
      v_7649 <- eval (handleImmediateWithSignExtend v_3096 8 8);
      v_7652 <- getRegister v_3100;
      v_7654 <- eval (concat (expression.bv_nat 24 0) v_7649);
      setRegister (lhs.of_reg v_3101) (mux (ugt (concat (expression.bv_nat 56 0) v_7649) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7652 0 32) v_7654) 0 32) (concat (extract (shl (extract v_7652 32 64) v_7654) 0 32) (concat (extract (shl (extract v_7652 64 96) v_7654) 0 32) (extract (shl (extract v_7652 96 128) v_7654) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3110 : reg (bv 128)) (v_3111 : reg (bv 128)) (v_3112 : reg (bv 128)) => do
      v_7676 <- getRegister v_3110;
      v_7679 <- getRegister v_3111;
      v_7681 <- eval (extract v_7676 96 128);
      setRegister (lhs.of_reg v_3112) (mux (ugt (extract v_7676 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7679 0 32) v_7681) 0 32) (concat (extract (shl (extract v_7679 32 64) v_7681) 0 32) (concat (extract (shl (extract v_7679 64 96) v_7681) 0 32) (extract (shl (extract v_7679 96 128) v_7681) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3113 : imm int) (v_3117 : reg (bv 256)) (v_3118 : reg (bv 256)) => do
      v_7698 <- eval (handleImmediateWithSignExtend v_3113 8 8);
      v_7701 <- getRegister v_3117;
      v_7703 <- eval (concat (expression.bv_nat 24 0) v_7698);
      setRegister (lhs.of_reg v_3118) (mux (ugt (concat (expression.bv_nat 56 0) v_7698) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7701 0 32) v_7703) 0 32) (concat (extract (shl (extract v_7701 32 64) v_7703) 0 32) (concat (extract (shl (extract v_7701 64 96) v_7703) 0 32) (concat (extract (shl (extract v_7701 96 128) v_7703) 0 32) (concat (extract (shl (extract v_7701 128 160) v_7703) 0 32) (concat (extract (shl (extract v_7701 160 192) v_7703) 0 32) (concat (extract (shl (extract v_7701 192 224) v_7703) 0 32) (extract (shl (extract v_7701 224 256) v_7703) 0 32)))))))));
      pure ()
    pat_end;
    pattern fun (v_3129 : reg (bv 128)) (v_3127 : reg (bv 256)) (v_3128 : reg (bv 256)) => do
      v_7741 <- getRegister v_3129;
      v_7744 <- getRegister v_3127;
      v_7746 <- eval (extract v_7741 96 128);
      setRegister (lhs.of_reg v_3128) (mux (ugt (extract v_7741 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7744 0 32) v_7746) 0 32) (concat (extract (shl (extract v_7744 32 64) v_7746) 0 32) (concat (extract (shl (extract v_7744 64 96) v_7746) 0 32) (concat (extract (shl (extract v_7744 96 128) v_7746) 0 32) (concat (extract (shl (extract v_7744 128 160) v_7746) 0 32) (concat (extract (shl (extract v_7744 160 192) v_7746) 0 32) (concat (extract (shl (extract v_7744 192 224) v_7746) 0 32) (extract (shl (extract v_7744 224 256) v_7746) 0 32)))))))));
      pure ()
    pat_end;
    pattern fun (v_3104 : Mem) (v_3105 : reg (bv 128)) (v_3106 : reg (bv 128)) => do
      v_13928 <- evaluateAddress v_3104;
      v_13929 <- load v_13928 16;
      v_13932 <- getRegister v_3105;
      v_13934 <- eval (extract v_13929 96 128);
      setRegister (lhs.of_reg v_3106) (mux (ugt (extract v_13929 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_13932 0 32) v_13934) 0 32) (concat (extract (shl (extract v_13932 32 64) v_13934) 0 32) (concat (extract (shl (extract v_13932 64 96) v_13934) 0 32) (extract (shl (extract v_13932 96 128) v_13934) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3121 : Mem) (v_3122 : reg (bv 256)) (v_3123 : reg (bv 256)) => do
      v_13951 <- evaluateAddress v_3121;
      v_13952 <- load v_13951 16;
      v_13955 <- getRegister v_3122;
      v_13957 <- eval (extract v_13952 96 128);
      setRegister (lhs.of_reg v_3123) (mux (ugt (extract v_13952 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_13955 0 32) v_13957) 0 32) (concat (extract (shl (extract v_13955 32 64) v_13957) 0 32) (concat (extract (shl (extract v_13955 64 96) v_13957) 0 32) (concat (extract (shl (extract v_13955 96 128) v_13957) 0 32) (concat (extract (shl (extract v_13955 128 160) v_13957) 0 32) (concat (extract (shl (extract v_13955 160 192) v_13957) 0 32) (concat (extract (shl (extract v_13955 192 224) v_13957) 0 32) (extract (shl (extract v_13955 224 256) v_13957) 0 32)))))))));
      pure ()
    pat_end
