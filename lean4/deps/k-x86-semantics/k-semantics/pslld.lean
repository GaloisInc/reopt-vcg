def pslld1 : instruction :=
  definst "pslld" $ do
    pattern fun (v_3019 : imm int) (v_3018 : reg (bv 128)) => do
      v_7531 <- eval (handleImmediateWithSignExtend v_3019 8 8);
      v_7534 <- getRegister v_3018;
      v_7536 <- eval (concat (expression.bv_nat 24 0) v_7531);
      setRegister (lhs.of_reg v_3018) (mux (ugt (concat (expression.bv_nat 56 0) v_7531) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7534 0 32) v_7536) 0 32) (concat (extract (shl (extract v_7534 32 64) v_7536) 0 32) (concat (extract (shl (extract v_7534 64 96) v_7536) 0 32) (extract (shl (extract v_7534 96 128) v_7536) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3027 : reg (bv 128)) (v_3028 : reg (bv 128)) => do
      v_7557 <- getRegister v_3027;
      v_7560 <- getRegister v_3028;
      v_7562 <- eval (extract v_7557 96 128);
      setRegister (lhs.of_reg v_3028) (mux (ugt (extract v_7557 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_7560 0 32) v_7562) 0 32) (concat (extract (shl (extract v_7560 32 64) v_7562) 0 32) (concat (extract (shl (extract v_7560 64 96) v_7562) 0 32) (extract (shl (extract v_7560 96 128) v_7562) 0 32)))));
      pure ()
    pat_end;
    pattern fun (v_3024 : Mem) (v_3023 : reg (bv 128)) => do
      v_14239 <- evaluateAddress v_3024;
      v_14240 <- load v_14239 16;
      v_14243 <- getRegister v_3023;
      v_14245 <- eval (extract v_14240 96 128);
      setRegister (lhs.of_reg v_3023) (mux (ugt (extract v_14240 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (extract (shl (extract v_14243 0 32) v_14245) 0 32) (concat (extract (shl (extract v_14243 32 64) v_14245) 0 32) (concat (extract (shl (extract v_14243 64 96) v_14245) 0 32) (extract (shl (extract v_14243 96 128) v_14245) 0 32)))));
      pure ()
    pat_end
