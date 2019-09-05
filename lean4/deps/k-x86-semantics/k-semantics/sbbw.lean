def sbbw1 : instruction :=
  definst "sbbw" $ do
    pattern fun (v_3356 : imm int) (v_3352 : reg (bv 16)) => do
      v_7692 <- getRegister cf;
      v_7694 <- eval (handleImmediateWithSignExtend v_3356 16 16);
      v_7696 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7694 (expression.bv_nat 16 65535)));
      v_7699 <- getRegister v_3352;
      v_7701 <- eval (add (mux (eq v_7692 (expression.bv_nat 1 1)) v_7696 (add v_7696 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_7699));
      v_7702 <- eval (extract v_7701 1 17);
      v_7704 <- eval (isBitSet v_7701 1);
      v_7709 <- eval (eq (bv_xor (extract v_7694 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3352) v_7702;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7694 v_7699) 11) (isBitSet v_7701 12)));
      setRegister cf (notBool_ (isBitSet v_7701 0));
      setRegister of (bit_and (eq v_7709 (isBitSet v_7699 0)) (notBool_ (eq v_7709 v_7704)));
      setRegister pf (parityFlag (extract v_7701 9 17));
      setRegister sf v_7704;
      setRegister zf (zeroFlag v_7702);
      pure ()
    pat_end;
    pattern fun (v_3361 : reg (bv 16)) (v_3362 : reg (bv 16)) => do
      v_7733 <- getRegister cf;
      v_7735 <- getRegister v_3361;
      v_7737 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7735 (expression.bv_nat 16 65535)));
      v_7740 <- getRegister v_3362;
      v_7742 <- eval (add (mux (eq v_7733 (expression.bv_nat 1 1)) v_7737 (add v_7737 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_7740));
      v_7743 <- eval (extract v_7742 1 17);
      v_7745 <- eval (isBitSet v_7742 1);
      v_7750 <- eval (eq (bv_xor (extract v_7735 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3362) v_7743;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7735 v_7740) 11) (isBitSet v_7742 12)));
      setRegister cf (notBool_ (isBitSet v_7742 0));
      setRegister of (bit_and (eq v_7750 (isBitSet v_7740 0)) (notBool_ (eq v_7750 v_7745)));
      setRegister pf (parityFlag (extract v_7742 9 17));
      setRegister sf v_7745;
      setRegister zf (zeroFlag v_7743);
      pure ()
    pat_end;
    pattern fun (v_3360 : Mem) (v_3357 : reg (bv 16)) => do
      v_11588 <- getRegister cf;
      v_11590 <- evaluateAddress v_3360;
      v_11591 <- load v_11590 2;
      v_11593 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_11591 (expression.bv_nat 16 65535)));
      v_11596 <- getRegister v_3357;
      v_11598 <- eval (add (mux (eq v_11588 (expression.bv_nat 1 1)) v_11593 (add v_11593 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_11596));
      v_11599 <- eval (extract v_11598 1 17);
      v_11601 <- eval (isBitSet v_11598 1);
      v_11606 <- eval (eq (bv_xor (extract v_11591 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3357) v_11599;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_11591 v_11596) 11) (isBitSet v_11598 12)));
      setRegister cf (notBool_ (isBitSet v_11598 0));
      setRegister of (bit_and (eq v_11606 (isBitSet v_11596 0)) (notBool_ (eq v_11606 v_11601)));
      setRegister pf (parityFlag (extract v_11598 9 17));
      setRegister sf v_11601;
      setRegister zf (zeroFlag v_11599);
      pure ()
    pat_end;
    pattern fun (v_3347 : imm int) (v_3346 : Mem) => do
      v_14405 <- evaluateAddress v_3346;
      v_14406 <- getRegister cf;
      v_14408 <- eval (handleImmediateWithSignExtend v_3347 16 16);
      v_14410 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14408 (expression.bv_nat 16 65535)));
      v_14413 <- load v_14405 2;
      v_14415 <- eval (add (mux (eq v_14406 (expression.bv_nat 1 1)) v_14410 (add v_14410 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_14413));
      v_14416 <- eval (extract v_14415 1 17);
      store v_14405 v_14416 2;
      v_14419 <- eval (isBitSet v_14415 1);
      v_14424 <- eval (eq (bv_xor (extract v_14408 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14408 v_14413) 11) (isBitSet v_14415 12)));
      setRegister cf (notBool_ (isBitSet v_14415 0));
      setRegister of (bit_and (eq v_14424 (isBitSet v_14413 0)) (notBool_ (eq v_14424 v_14419)));
      setRegister pf (parityFlag (extract v_14415 9 17));
      setRegister sf v_14419;
      setRegister zf (zeroFlag v_14416);
      pure ()
    pat_end;
    pattern fun (v_3348 : reg (bv 16)) (v_3351 : Mem) => do
      v_14443 <- evaluateAddress v_3351;
      v_14444 <- getRegister cf;
      v_14446 <- getRegister v_3348;
      v_14448 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14446 (expression.bv_nat 16 65535)));
      v_14451 <- load v_14443 2;
      v_14453 <- eval (add (mux (eq v_14444 (expression.bv_nat 1 1)) v_14448 (add v_14448 (expression.bv_nat 17 1))) (concat (expression.bv_nat 1 0) v_14451));
      v_14454 <- eval (extract v_14453 1 17);
      store v_14443 v_14454 2;
      v_14457 <- eval (isBitSet v_14453 1);
      v_14462 <- eval (eq (bv_xor (extract v_14446 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14446 v_14451) 11) (isBitSet v_14453 12)));
      setRegister cf (notBool_ (isBitSet v_14453 0));
      setRegister of (bit_and (eq v_14462 (isBitSet v_14451 0)) (notBool_ (eq v_14462 v_14457)));
      setRegister pf (parityFlag (extract v_14453 9 17));
      setRegister sf v_14457;
      setRegister zf (zeroFlag v_14454);
      pure ()
    pat_end
