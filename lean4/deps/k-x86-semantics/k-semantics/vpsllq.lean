def vpsllq1 : instruction :=
  definst "vpsllq" $ do
    pattern fun (v_3171 : imm int) (v_3173 : reg (bv 128)) (v_3174 : reg (bv 128)) => do
      v_7832 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3171 8 8));
      v_7834 <- getRegister v_3173;
      setRegister (lhs.of_reg v_3174) (mux (ugt v_7832 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7834 0 64) v_7832) 0 64) (extract (shl (extract v_7834 64 128) v_7832) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3183 : reg (bv 128)) (v_3184 : reg (bv 128)) (v_3185 : reg (bv 128)) => do
      v_7849 <- getRegister v_3183;
      v_7850 <- eval (extract v_7849 64 128);
      v_7852 <- getRegister v_3184;
      setRegister (lhs.of_reg v_3185) (mux (ugt v_7850 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7852 0 64) v_7850) 0 64) (extract (shl (extract v_7852 64 128) v_7850) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3188 : imm int) (v_3190 : reg (bv 256)) (v_3191 : reg (bv 256)) => do
      v_7863 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3188 8 8));
      v_7865 <- getRegister v_3190;
      setRegister (lhs.of_reg v_3191) (mux (ugt v_7863 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7865 0 64) v_7863) 0 64) (concat (extract (shl (extract v_7865 64 128) v_7863) 0 64) (concat (extract (shl (extract v_7865 128 192) v_7863) 0 64) (extract (shl (extract v_7865 192 256) v_7863) 0 64)))));
      pure ()
    pat_end;
    pattern fun (v_3202 : reg (bv 128)) (v_3200 : reg (bv 256)) (v_3201 : reg (bv 256)) => do
      v_7888 <- getRegister v_3202;
      v_7889 <- eval (extract v_7888 64 128);
      v_7891 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3201) (mux (ugt v_7889 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_7891 0 64) v_7889) 0 64) (concat (extract (shl (extract v_7891 64 128) v_7889) 0 64) (concat (extract (shl (extract v_7891 128 192) v_7889) 0 64) (extract (shl (extract v_7891 192 256) v_7889) 0 64)))));
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3178 : reg (bv 128)) (v_3179 : reg (bv 128)) => do
      v_14017 <- evaluateAddress v_3177;
      v_14018 <- load v_14017 16;
      v_14019 <- eval (extract v_14018 64 128);
      v_14021 <- getRegister v_3178;
      setRegister (lhs.of_reg v_3179) (mux (ugt v_14019 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14021 0 64) v_14019) 0 64) (extract (shl (extract v_14021 64 128) v_14019) 0 64)));
      pure ()
    pat_end;
    pattern fun (v_3194 : Mem) (v_3195 : reg (bv 256)) (v_3196 : reg (bv 256)) => do
      v_14031 <- evaluateAddress v_3194;
      v_14032 <- load v_14031 16;
      v_14033 <- eval (extract v_14032 64 128);
      v_14035 <- getRegister v_3195;
      setRegister (lhs.of_reg v_3196) (mux (ugt v_14033 (expression.bv_nat 64 63)) (expression.bv_nat 256 0) (concat (extract (shl (extract v_14035 0 64) v_14033) 0 64) (concat (extract (shl (extract v_14035 64 128) v_14033) 0 64) (concat (extract (shl (extract v_14035 128 192) v_14033) 0 64) (extract (shl (extract v_14035 192 256) v_14033) 0 64)))));
      pure ()
    pat_end
