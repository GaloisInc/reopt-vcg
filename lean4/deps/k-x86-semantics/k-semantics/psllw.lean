def psllw1 : instruction :=
  definst "psllw" $ do
    pattern fun (v_3079 : imm int) (v_3080 : reg (bv 128)) => do
      v_7646 <- eval (handleImmediateWithSignExtend v_3079 8 8);
      v_7649 <- getRegister v_3080;
      v_7651 <- eval (concat (expression.bv_nat 8 0) v_7646);
      setRegister (lhs.of_reg v_3080) (mux (ugt (concat (expression.bv_nat 56 0) v_7646) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7649 0 16) v_7651) 0 16) (concat (extract (shl (extract v_7649 16 32) v_7651) 0 16) (concat (extract (shl (extract v_7649 32 48) v_7651) 0 16) (concat (extract (shl (extract v_7649 48 64) v_7651) 0 16) (concat (extract (shl (extract v_7649 64 80) v_7651) 0 16) (concat (extract (shl (extract v_7649 80 96) v_7651) 0 16) (concat (extract (shl (extract v_7649 96 112) v_7651) 0 16) (extract (shl (extract v_7649 112 128) v_7651) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3088 : reg (bv 128)) (v_3089 : reg (bv 128)) => do
      v_7688 <- getRegister v_3088;
      v_7691 <- getRegister v_3089;
      v_7693 <- eval (extract v_7688 112 128);
      setRegister (lhs.of_reg v_3089) (mux (ugt (extract v_7688 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7691 0 16) v_7693) 0 16) (concat (extract (shl (extract v_7691 16 32) v_7693) 0 16) (concat (extract (shl (extract v_7691 32 48) v_7693) 0 16) (concat (extract (shl (extract v_7691 48 64) v_7693) 0 16) (concat (extract (shl (extract v_7691 64 80) v_7693) 0 16) (concat (extract (shl (extract v_7691 80 96) v_7693) 0 16) (concat (extract (shl (extract v_7691 96 112) v_7693) 0 16) (extract (shl (extract v_7691 112 128) v_7693) 0 16)))))))));
      pure ()
    pat_end;
    pattern fun (v_3084 : Mem) (v_3085 : reg (bv 128)) => do
      v_14252 <- evaluateAddress v_3084;
      v_14253 <- load v_14252 16;
      v_14256 <- getRegister v_3085;
      v_14258 <- eval (extract v_14253 112 128);
      setRegister (lhs.of_reg v_3085) (mux (ugt (extract v_14253 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14256 0 16) v_14258) 0 16) (concat (extract (shl (extract v_14256 16 32) v_14258) 0 16) (concat (extract (shl (extract v_14256 32 48) v_14258) 0 16) (concat (extract (shl (extract v_14256 48 64) v_14258) 0 16) (concat (extract (shl (extract v_14256 64 80) v_14258) 0 16) (concat (extract (shl (extract v_14256 80 96) v_14258) 0 16) (concat (extract (shl (extract v_14256 96 112) v_14258) 0 16) (extract (shl (extract v_14256 112 128) v_14258) 0 16)))))))));
      pure ()
    pat_end
