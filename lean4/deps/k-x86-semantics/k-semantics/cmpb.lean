def cmpb1 : instruction :=
  definst "cmpb" $ do
    pattern fun (v_3398 : imm int) (v_3400 : reg (bv 8)) => do
      v_5409 <- eval (handleImmediateWithSignExtend v_3398 8 8);
      v_5413 <- getRegister v_3400;
      v_5415 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5409 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5413));
      v_5416 <- eval (extract v_5415 1 9);
      v_5418 <- eval (isBitSet v_5415 1);
      v_5422 <- eval (eq (bv_xor (extract v_5409 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5409 v_5413) 3) (isBitSet v_5415 4)));
      setRegister cf (notBool_ (isBitSet v_5415 0));
      setRegister of (bit_and (eq v_5422 (isBitSet v_5413 0)) (notBool_ (eq v_5422 v_5418)));
      setRegister pf (parityFlag v_5416);
      setRegister sf v_5418;
      setRegister zf (zeroFlag v_5416);
      pure ()
    pat_end;
    pattern fun (v_3413 : reg (bv 8)) (v_3414 : reg (bv 8)) => do
      v_5477 <- getRegister v_3413;
      v_5481 <- getRegister v_3414;
      v_5483 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5477 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5481));
      v_5484 <- eval (extract v_5483 1 9);
      v_5486 <- eval (isBitSet v_5483 1);
      v_5490 <- eval (eq (bv_xor (extract v_5477 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5477 v_5481) 3) (isBitSet v_5483 4)));
      setRegister cf (notBool_ (isBitSet v_5483 0));
      setRegister of (bit_and (eq v_5490 (isBitSet v_5481 0)) (notBool_ (eq v_5490 v_5486)));
      setRegister pf (parityFlag v_5484);
      setRegister sf v_5486;
      setRegister zf (zeroFlag v_5484);
      pure ()
    pat_end;
    pattern fun (v_3367 : imm int) (v_3368 : Mem) => do
      v_8632 <- eval (handleImmediateWithSignExtend v_3367 8 8);
      v_8636 <- evaluateAddress v_3368;
      v_8637 <- load v_8636 1;
      v_8639 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8632 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8637));
      v_8640 <- eval (extract v_8639 1 9);
      v_8642 <- eval (isBitSet v_8639 1);
      v_8646 <- eval (eq (bv_xor (extract v_8632 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8632 v_8637) 3) (isBitSet v_8639 4)));
      setRegister cf (notBool_ (isBitSet v_8639 0));
      setRegister of (bit_and (eq v_8646 (isBitSet v_8637 0)) (notBool_ (eq v_8646 v_8642)));
      setRegister pf (parityFlag v_8640);
      setRegister sf v_8642;
      setRegister zf (zeroFlag v_8640);
      pure ()
    pat_end;
    pattern fun (v_3376 : reg (bv 8)) (v_3375 : Mem) => do
      v_8698 <- getRegister v_3376;
      v_8702 <- evaluateAddress v_3375;
      v_8703 <- load v_8702 1;
      v_8705 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8698 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8703));
      v_8706 <- eval (extract v_8705 1 9);
      v_8708 <- eval (isBitSet v_8705 1);
      v_8712 <- eval (eq (bv_xor (extract v_8698 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8698 v_8703) 3) (isBitSet v_8705 4)));
      setRegister cf (notBool_ (isBitSet v_8705 0));
      setRegister of (bit_and (eq v_8712 (isBitSet v_8703 0)) (notBool_ (eq v_8712 v_8708)));
      setRegister pf (parityFlag v_8706);
      setRegister sf v_8708;
      setRegister zf (zeroFlag v_8706);
      pure ()
    pat_end;
    pattern fun (v_3403 : Mem) (v_3404 : reg (bv 8)) => do
      v_8764 <- evaluateAddress v_3403;
      v_8765 <- load v_8764 1;
      v_8769 <- getRegister v_3404;
      v_8771 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8765 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8769));
      v_8772 <- eval (extract v_8771 1 9);
      v_8774 <- eval (isBitSet v_8771 1);
      v_8778 <- eval (eq (bv_xor (extract v_8765 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8765 v_8769) 3) (isBitSet v_8771 4)));
      setRegister cf (notBool_ (isBitSet v_8771 0));
      setRegister of (bit_and (eq v_8778 (isBitSet v_8769 0)) (notBool_ (eq v_8778 v_8774)));
      setRegister pf (parityFlag v_8772);
      setRegister sf v_8774;
      setRegister zf (zeroFlag v_8772);
      pure ()
    pat_end
