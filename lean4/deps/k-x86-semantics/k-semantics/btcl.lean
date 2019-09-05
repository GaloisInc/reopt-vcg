def btcl1 : instruction :=
  definst "btcl" $ do
    pattern fun (v_3083 : imm int) (v_3085 : reg (bv 32)) => do
      v_5956 <- getRegister v_3085;
      v_5959 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3083 8 8) (expression.bv_nat 8 31)) 32);
      setRegister (lhs.of_reg v_3085) (bv_xor v_5956 (extract (shl (expression.bv_nat 32 1) v_5959) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5956 v_5959) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3089 : reg (bv 32)) (v_3090 : reg (bv 32)) => do
      v_5971 <- getRegister v_3090;
      v_5972 <- getRegister v_3089;
      v_5973 <- eval (bv_and v_5972 (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_3090) (bv_xor v_5971 (extract (shl (expression.bv_nat 32 1) v_5973) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5971 v_5973) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3075 : imm int) (v_3077 : Mem) => do
      v_10739 <- evaluateAddress v_3077;
      v_10740 <- eval (handleImmediateWithSignExtend v_3075 8 8);
      v_10744 <- eval (add v_10739 (concat (expression.bv_nat 59 0) (bv_and (extract v_10740 0 5) (expression.bv_nat 5 3))));
      v_10745 <- load v_10744 1;
      v_10748 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10740 5 8) (expression.bv_nat 3 7)));
      store v_10744 (bv_xor v_10745 (extract (shl (expression.bv_nat 8 1) v_10748) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10745 v_10748) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3080 : reg (bv 32)) (v_3081 : Mem) => do
      v_10760 <- evaluateAddress v_3081;
      v_10761 <- getRegister v_3080;
      v_10765 <- eval (add v_10760 (concat (expression.bv_nat 3 0) (extract (sext v_10761 64) 0 61)));
      v_10766 <- load v_10765 1;
      v_10768 <- eval (concat (expression.bv_nat 5 0) (extract v_10761 29 32));
      store v_10765 (bv_xor v_10766 (extract (shl (expression.bv_nat 8 1) v_10768) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10766 v_10768) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
