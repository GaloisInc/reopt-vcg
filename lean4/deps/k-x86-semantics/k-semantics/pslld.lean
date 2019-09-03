def pslld1 : instruction :=
  definst "pslld" $ do
    pattern fun (v_2969 : imm int) (v_2970 : reg (bv 128)) => do
      v_7528 <- eval (handleImmediateWithSignExtend v_2969 8 8);
      v_7531 <- getRegister v_2970;
      v_7534 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7528));
      setRegister (lhs.of_reg v_2970) (mux (ugt (concat (expression.bv_nat 56 0) v_7528) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7531 0 32) v_7534) 0 32) (concat (extract (shl (extract v_7531 32 64) v_7534) 0 32) (concat (extract (shl (extract v_7531 64 96) v_7534) 0 32) (extract (shl (extract v_7531 96 128) v_7534) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_2978 : reg (bv 128)) (v_2979 : reg (bv 128)) => do
      v_7555 <- getRegister v_2978;
      v_7558 <- getRegister v_2979;
      v_7561 <- eval (uvalueMInt (extract v_7555 96 128));
      setRegister (lhs.of_reg v_2979) (mux (ugt (extract v_7555 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7558 0 32) v_7561) 0 32) (concat (extract (shl (extract v_7558 32 64) v_7561) 0 32) (concat (extract (shl (extract v_7558 64 96) v_7561) 0 32) (extract (shl (extract v_7558 96 128) v_7561) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_2974 : Mem) (v_2975 : reg (bv 128)) => do
      v_14409 <- evaluateAddress v_2974;
      v_14410 <- load v_14409 16;
      v_14413 <- getRegister v_2975;
      v_14416 <- eval (uvalueMInt (extract v_14410 96 128));
      setRegister (lhs.of_reg v_2975) (mux (ugt (extract v_14410 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14413 0 32) v_14416) 0 32) (concat (extract (shl (extract v_14413 32 64) v_14416) 0 32) (concat (extract (shl (extract v_14413 64 96) v_14416) 0 32) (extract (shl (extract v_14413 96 128) v_14416) 0 32)))));
      pure ()
    pat_end
