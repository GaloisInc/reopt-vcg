def pslld1 : instruction :=
  definst "pslld" $ do
    pattern fun (v_3046 : imm int) (v_3047 : reg (bv 128)) => do
      v_7558 <- eval (handleImmediateWithSignExtend v_3046 8 8);
      v_7561 <- getRegister v_3047;
      v_7563 <- eval (concat (expression.bv_nat 24 0) v_7558);
      setRegister (lhs.of_reg v_3047) (mux (ugt (concat (expression.bv_nat 56 0) v_7558) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7561 0 32) v_7563) 0 32) (concat (extract (shl (extract v_7561 32 64) v_7563) 0 32) (concat (extract (shl (extract v_7561 64 96) v_7563) 0 32) (extract (shl (extract v_7561 96 128) v_7563) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3055 : reg (bv 128)) (v_3056 : reg (bv 128)) => do
      v_7584 <- getRegister v_3055;
      v_7587 <- getRegister v_3056;
      v_7589 <- eval (extract v_7584 96 128);
      setRegister (lhs.of_reg v_3056) (mux (ugt (extract v_7584 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7587 0 32) v_7589) 0 32) (concat (extract (shl (extract v_7587 32 64) v_7589) 0 32) (concat (extract (shl (extract v_7587 64 96) v_7589) 0 32) (extract (shl (extract v_7587 96 128) v_7589) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3051 : Mem) (v_3052 : reg (bv 128)) => do
      v_14215 <- evaluateAddress v_3051;
      v_14216 <- load v_14215 16;
      v_14219 <- getRegister v_3052;
      v_14221 <- eval (extract v_14216 96 128);
      setRegister (lhs.of_reg v_3052) (mux (ugt (extract v_14216 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14219 0 32) v_14221) 0 32) (concat (extract (shl (extract v_14219 32 64) v_14221) 0 32) (concat (extract (shl (extract v_14219 64 96) v_14221) 0 32) (extract (shl (extract v_14219 96 128) v_14221) 0 32)))));
      pure ()
    pat_end
