def vpsllq1 : instruction :=
  definst "vpsllq" $ do
    pattern fun (v_3142 : imm int) (v_3146 : reg (bv 128)) (v_3147 : reg (bv 128)) => do
      v_7805 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3142 8 8));
      v_7807 <- getRegister v_3146;
      setRegister (lhs.of_reg v_3147) (mux (ugt v_7805 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7807 0 64) v_7805) 0 64) (extract (shl (extract v_7807 64 128) v_7805) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3156 : reg (bv 128)) (v_3157 : reg (bv 128)) (v_3158 : reg (bv 128)) => do
      v_7822 <- getRegister v_3156;
      v_7823 <- eval (extract v_7822 64 128);
      v_7825 <- getRegister v_3157;
      setRegister (lhs.of_reg v_3158) (mux (ugt v_7823 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7825 0 64) v_7823) 0 64) (extract (shl (extract v_7825 64 128) v_7823) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3159 : imm int) (v_3163 : reg (bv 256)) (v_3164 : reg (bv 256)) => do
      v_7836 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3159 8 8));
      v_7838 <- getRegister v_3163;
      setRegister (lhs.of_reg v_3164) (mux (ugt v_7836 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7838 0 64) v_7836) 0 64) (concat (extract (shl (extract v_7838 64 128) v_7836) 0 64) (concat (extract (shl (extract v_7838 128 192) v_7836) 0 64) (extract (shl (extract v_7838 192 256) v_7836) 0 64)))));
      pure ()
    pat_end;
    pattern fun (v_3175 : reg (bv 128)) (v_3173 : reg (bv 256)) (v_3174 : reg (bv 256)) => do
      v_7861 <- getRegister v_3175;
      v_7862 <- eval (extract v_7861 64 128);
      v_7864 <- getRegister v_3173;
      setRegister (lhs.of_reg v_3174) (mux (ugt v_7862 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7864 0 64) v_7862) 0 64) (concat (extract (shl (extract v_7864 64 128) v_7862) 0 64) (concat (extract (shl (extract v_7864 128 192) v_7862) 0 64) (extract (shl (extract v_7864 192 256) v_7862) 0 64)))));
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3151 : reg (bv 128)) (v_3152 : reg (bv 128)) => do
      v_13990 <- evaluateAddress v_3150;
      v_13991 <- load v_13990 16;
      v_13992 <- eval (extract v_13991 64 128);
      v_13994 <- getRegister v_3151;
      setRegister (lhs.of_reg v_3152) (mux (ugt v_13992 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_13994 0 64) v_13992) 0 64) (extract (shl (extract v_13994 64 128) v_13992) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3167 : Mem) (v_3168 : reg (bv 256)) (v_3169 : reg (bv 256)) => do
      v_14004 <- evaluateAddress v_3167;
      v_14005 <- load v_14004 16;
      v_14006 <- eval (extract v_14005 64 128);
      v_14008 <- getRegister v_3168;
      setRegister (lhs.of_reg v_3169) (mux (ugt v_14006 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14008 0 64) v_14006) 0 64) (concat (extract (shl (extract v_14008 64 128) v_14006) 0 64) (concat (extract (shl (extract v_14008 128 192) v_14006) 0 64) (extract (shl (extract v_14008 192 256) v_14006) 0 64)))));
      pure ()
    pat_end
