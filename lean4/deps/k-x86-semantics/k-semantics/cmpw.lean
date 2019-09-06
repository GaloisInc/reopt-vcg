def cmpw1 : instruction :=
  definst "cmpw" $ do
    pattern fun (v_2509 : imm int) (v_2510 : reg (bv 16)) => do
      v_3980 <- eval (handleImmediateWithSignExtend v_2509 16 16);
      v_3984 <- getRegister v_2510;
      v_3986 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3980 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_3984));
      v_3989 <- eval (isBitSet v_3986 1);
      v_3994 <- eval (eq (bv_xor (extract v_3980 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3980 v_3984) 11) (isBitSet v_3986 12)));
      setRegister cf (isBitClear v_3986 0);
      setRegister of (bit_and (eq v_3994 (isBitSet v_3984 0)) (notBool_ (eq v_3994 v_3989)));
      setRegister pf (parityFlag (extract v_3986 9 17));
      setRegister sf v_3989;
      setRegister zf (zeroFlag (extract v_3986 1 17));
      pure ()
    pat_end;
    pattern fun (v_2518 : reg (bv 16)) (v_2519 : reg (bv 16)) => do
      v_4016 <- getRegister v_2518;
      v_4020 <- getRegister v_2519;
      v_4022 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_4016 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_4020));
      v_4025 <- eval (isBitSet v_4022 1);
      v_4030 <- eval (eq (bv_xor (extract v_4016 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4016 v_4020) 11) (isBitSet v_4022 12)));
      setRegister cf (isBitClear v_4022 0);
      setRegister of (bit_and (eq v_4030 (isBitSet v_4020 0)) (notBool_ (eq v_4030 v_4025)));
      setRegister pf (parityFlag (extract v_4022 9 17));
      setRegister sf v_4025;
      setRegister zf (zeroFlag (extract v_4022 1 17));
      pure ()
    pat_end;
    pattern fun (v_2502 : imm int) (v_2501 : Mem) => do
      v_7674 <- eval (handleImmediateWithSignExtend v_2502 16 16);
      v_7678 <- evaluateAddress v_2501;
      v_7679 <- load v_7678 2;
      v_7681 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7674 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7679));
      v_7684 <- eval (isBitSet v_7681 1);
      v_7689 <- eval (eq (bv_xor (extract v_7674 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7674 v_7679) 11) (isBitSet v_7681 12)));
      setRegister cf (isBitClear v_7681 0);
      setRegister of (bit_and (eq v_7689 (isBitSet v_7679 0)) (notBool_ (eq v_7689 v_7684)));
      setRegister pf (parityFlag (extract v_7681 9 17));
      setRegister sf v_7684;
      setRegister zf (zeroFlag (extract v_7681 1 17));
      pure ()
    pat_end;
    pattern fun (v_2506 : reg (bv 16)) (v_2505 : Mem) => do
      v_7707 <- getRegister v_2506;
      v_7711 <- evaluateAddress v_2505;
      v_7712 <- load v_7711 2;
      v_7714 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7707 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7712));
      v_7717 <- eval (isBitSet v_7714 1);
      v_7722 <- eval (eq (bv_xor (extract v_7707 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7707 v_7712) 11) (isBitSet v_7714 12)));
      setRegister cf (isBitClear v_7714 0);
      setRegister of (bit_and (eq v_7722 (isBitSet v_7712 0)) (notBool_ (eq v_7722 v_7717)));
      setRegister pf (parityFlag (extract v_7714 9 17));
      setRegister sf v_7717;
      setRegister zf (zeroFlag (extract v_7714 1 17));
      pure ()
    pat_end;
    pattern fun (v_2514 : Mem) (v_2515 : reg (bv 16)) => do
      v_7740 <- evaluateAddress v_2514;
      v_7741 <- load v_7740 2;
      v_7745 <- getRegister v_2515;
      v_7747 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7741 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7745));
      v_7750 <- eval (isBitSet v_7747 1);
      v_7755 <- eval (eq (bv_xor (extract v_7741 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7741 v_7745) 11) (isBitSet v_7747 12)));
      setRegister cf (isBitClear v_7747 0);
      setRegister of (bit_and (eq v_7755 (isBitSet v_7745 0)) (notBool_ (eq v_7755 v_7750)));
      setRegister pf (parityFlag (extract v_7747 9 17));
      setRegister sf v_7750;
      setRegister zf (zeroFlag (extract v_7747 1 17));
      pure ()
    pat_end
