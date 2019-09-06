def vpslld1 : instruction :=
  definst "vpslld" $ do
    pattern fun (v_3125 : imm int) (v_3127 : reg (bv 128)) (v_3128 : reg (bv 128)) => do
      v_7676 <- eval (handleImmediateWithSignExtend v_3125 8 8);
      v_7679 <- getRegister v_3127;
      v_7681 <- eval (concat (expression.bv_nat 24 0) v_7676);
      setRegister (lhs.of_reg v_3128) (mux (ugt (concat (expression.bv_nat 56 0) v_7676) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7679 0 32) v_7681) 0 32) (concat (extract (shl (extract v_7679 32 64) v_7681) 0 32) (concat (extract (shl (extract v_7679 64 96) v_7681) 0 32) (extract (shl (extract v_7679 96 128) v_7681) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3137 : reg (bv 128)) (v_3138 : reg (bv 128)) (v_3139 : reg (bv 128)) => do
      v_7703 <- getRegister v_3137;
      v_7706 <- getRegister v_3138;
      v_7708 <- eval (extract v_7703 96 128);
      setRegister (lhs.of_reg v_3139) (mux (ugt (extract v_7703 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7706 0 32) v_7708) 0 32) (concat (extract (shl (extract v_7706 32 64) v_7708) 0 32) (concat (extract (shl (extract v_7706 64 96) v_7708) 0 32) (extract (shl (extract v_7706 96 128) v_7708) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3142 : imm int) (v_3144 : reg (bv 256)) (v_3145 : reg (bv 256)) => do
      v_7725 <- eval (handleImmediateWithSignExtend v_3142 8 8);
      v_7728 <- getRegister v_3144;
      v_7730 <- eval (concat (expression.bv_nat 24 0) v_7725);
      setRegister (lhs.of_reg v_3145) (mux (ugt (concat (expression.bv_nat 56 0) v_7725) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7728 0 32) v_7730) 0 32) (concat (extract (shl (extract v_7728 32 64) v_7730) 0 32) (concat (extract (shl (extract v_7728 64 96) v_7730) 0 32) (concat (extract (shl (extract v_7728 96 128) v_7730) 0 32) (concat (extract (shl (extract v_7728 128 160) v_7730) 0 32) (concat (extract (shl (extract v_7728 160 192) v_7730) 0 32) (concat (extract (shl (extract v_7728 192 224) v_7730) 0 32) (extract (shl (extract v_7728 224 256) v_7730) 0 32)))))))));
      pure ()
    pat_end;
    pattern fun (v_3156 : reg (bv 128)) (v_3154 : reg (bv 256)) (v_3155 : reg (bv 256)) => do
      v_7768 <- getRegister v_3156;
      v_7771 <- getRegister v_3154;
      v_7773 <- eval (extract v_7768 96 128);
      setRegister (lhs.of_reg v_3155) (mux (ugt (extract v_7768 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7771 0 32) v_7773) 0 32) (concat (extract (shl (extract v_7771 32 64) v_7773) 0 32) (concat (extract (shl (extract v_7771 64 96) v_7773) 0 32) (concat (extract (shl (extract v_7771 96 128) v_7773) 0 32) (concat (extract (shl (extract v_7771 128 160) v_7773) 0 32) (concat (extract (shl (extract v_7771 160 192) v_7773) 0 32) (concat (extract (shl (extract v_7771 192 224) v_7773) 0 32) (extract (shl (extract v_7771 224 256) v_7773) 0 32)))))))));
      pure ()
    pat_end;
    pattern fun (v_3131 : Mem) (v_3132 : reg (bv 128)) (v_3133 : reg (bv 128)) => do
      v_13955 <- evaluateAddress v_3131;
      v_13956 <- load v_13955 16;
      v_13959 <- getRegister v_3132;
      v_13961 <- eval (extract v_13956 96 128);
      setRegister (lhs.of_reg v_3133) (mux (ugt (extract v_13956 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_13959 0 32) v_13961) 0 32) (concat (extract (shl (extract v_13959 32 64) v_13961) 0 32) (concat (extract (shl (extract v_13959 64 96) v_13961) 0 32) (extract (shl (extract v_13959 96 128) v_13961) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3148 : Mem) (v_3149 : reg (bv 256)) (v_3150 : reg (bv 256)) => do
      v_13978 <- evaluateAddress v_3148;
      v_13979 <- load v_13978 16;
      v_13982 <- getRegister v_3149;
      v_13984 <- eval (extract v_13979 96 128);
      setRegister (lhs.of_reg v_3150) (mux (ugt (extract v_13979 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_13982 0 32) v_13984) 0 32) (concat (extract (shl (extract v_13982 32 64) v_13984) 0 32) (concat (extract (shl (extract v_13982 64 96) v_13984) 0 32) (concat (extract (shl (extract v_13982 96 128) v_13984) 0 32) (concat (extract (shl (extract v_13982 128 160) v_13984) 0 32) (concat (extract (shl (extract v_13982 160 192) v_13984) 0 32) (concat (extract (shl (extract v_13982 192 224) v_13984) 0 32) (extract (shl (extract v_13982 224 256) v_13984) 0 32)))))))));
      pure ()
    pat_end
