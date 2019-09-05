def sarl1 : instruction :=
  definst "sarl" $ do
    pattern fun cl (v_3121 : reg (bv 32)) => do
      v_6672 <- getRegister rcx;
      v_6674 <- eval (bv_and (extract v_6672 56 64) (expression.bv_nat 8 31));
      v_6675 <- eval (eq v_6674 (expression.bv_nat 8 0));
      v_6676 <- eval (notBool_ v_6675);
      v_6677 <- getRegister v_3121;
      v_6680 <- eval (ashr (concat v_6677 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_6674));
      v_6681 <- eval (extract v_6680 0 32);
      v_6684 <- getRegister zf;
      v_6690 <- getRegister sf;
      v_6697 <- getRegister pf;
      v_6703 <- eval (bit_and v_6676 undef);
      v_6704 <- getRegister of;
      v_6711 <- getRegister cf;
      v_6715 <- getRegister af;
      setRegister (lhs.of_reg v_3121) v_6681;
      setRegister af (bit_or v_6703 (bit_and v_6675 (eq v_6715 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6676 (isBitSet v_6680 32)) (bit_and v_6675 (eq v_6711 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6674 (expression.bv_nat 8 1))) (bit_or v_6703 (bit_and v_6675 (eq v_6704 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6676 (parityFlag (extract v_6680 24 32))) (bit_and v_6675 (eq v_6697 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6676 (isBitSet v_6680 0)) (bit_and v_6675 (eq v_6690 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6676 (eq v_6681 (expression.bv_nat 32 0))) (bit_and v_6675 (eq v_6684 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3124 : imm int) (v_3126 : reg (bv 32)) => do
      v_6727 <- eval (bv_and (handleImmediateWithSignExtend v_3124 8 8) (expression.bv_nat 8 31));
      v_6728 <- eval (eq v_6727 (expression.bv_nat 8 0));
      v_6729 <- eval (notBool_ v_6728);
      v_6730 <- getRegister v_3126;
      v_6733 <- eval (ashr (concat v_6730 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_6727));
      v_6734 <- eval (extract v_6733 0 32);
      v_6737 <- getRegister zf;
      v_6743 <- getRegister sf;
      v_6750 <- getRegister pf;
      v_6756 <- eval (bit_and v_6729 undef);
      v_6757 <- getRegister of;
      v_6764 <- getRegister cf;
      v_6768 <- getRegister af;
      setRegister (lhs.of_reg v_3126) v_6734;
      setRegister af (bit_or v_6756 (bit_and v_6728 (eq v_6768 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6729 (isBitSet v_6733 32)) (bit_and v_6728 (eq v_6764 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6727 (expression.bv_nat 8 1))) (bit_or v_6756 (bit_and v_6728 (eq v_6757 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6729 (parityFlag (extract v_6733 24 32))) (bit_and v_6728 (eq v_6750 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6729 (isBitSet v_6733 0)) (bit_and v_6728 (eq v_6743 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6729 (eq v_6734 (expression.bv_nat 32 0))) (bit_and v_6728 (eq v_6737 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3129 : reg (bv 32)) => do
      v_8468 <- getRegister v_3129;
      v_8470 <- eval (ashr (concat v_8468 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_8471 <- eval (extract v_8470 0 32);
      setRegister (lhs.of_reg v_3129) v_8471;
      setRegister af undef;
      setRegister cf (isBitSet v_8470 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8470 24 32));
      setRegister sf (isBitSet v_8470 0);
      setRegister zf (zeroFlag v_8471);
      pure ()
    pat_end;
    pattern fun cl (v_3107 : Mem) => do
      v_13695 <- evaluateAddress v_3107;
      v_13696 <- load v_13695 4;
      v_13698 <- getRegister rcx;
      v_13700 <- eval (bv_and (extract v_13698 56 64) (expression.bv_nat 8 31));
      v_13702 <- eval (ashr (concat v_13696 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_13700));
      v_13703 <- eval (extract v_13702 0 32);
      store v_13695 v_13703 4;
      v_13705 <- eval (eq v_13700 (expression.bv_nat 8 0));
      v_13706 <- eval (notBool_ v_13705);
      v_13709 <- getRegister zf;
      v_13715 <- getRegister sf;
      v_13722 <- getRegister pf;
      v_13728 <- eval (bit_and v_13706 undef);
      v_13729 <- getRegister of;
      v_13736 <- getRegister cf;
      v_13740 <- getRegister af;
      setRegister af (bit_or v_13728 (bit_and v_13705 (eq v_13740 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13706 (isBitSet v_13702 32)) (bit_and v_13705 (eq v_13736 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13700 (expression.bv_nat 8 1))) (bit_or v_13728 (bit_and v_13705 (eq v_13729 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13706 (parityFlag (extract v_13702 24 32))) (bit_and v_13705 (eq v_13722 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13706 (isBitSet v_13702 0)) (bit_and v_13705 (eq v_13715 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13706 (eq v_13703 (expression.bv_nat 32 0))) (bit_and v_13705 (eq v_13709 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3110 : imm int) (v_3111 : Mem) => do
      v_13750 <- evaluateAddress v_3111;
      v_13751 <- load v_13750 4;
      v_13754 <- eval (bv_and (handleImmediateWithSignExtend v_3110 8 8) (expression.bv_nat 8 31));
      v_13756 <- eval (ashr (concat v_13751 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_13754));
      v_13757 <- eval (extract v_13756 0 32);
      store v_13750 v_13757 4;
      v_13759 <- eval (eq v_13754 (expression.bv_nat 8 0));
      v_13760 <- eval (notBool_ v_13759);
      v_13763 <- getRegister zf;
      v_13769 <- getRegister sf;
      v_13776 <- getRegister pf;
      v_13782 <- eval (bit_and v_13760 undef);
      v_13783 <- getRegister of;
      v_13790 <- getRegister cf;
      v_13794 <- getRegister af;
      setRegister af (bit_or v_13782 (bit_and v_13759 (eq v_13794 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13760 (isBitSet v_13756 32)) (bit_and v_13759 (eq v_13790 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13754 (expression.bv_nat 8 1))) (bit_or v_13782 (bit_and v_13759 (eq v_13783 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13760 (parityFlag (extract v_13756 24 32))) (bit_and v_13759 (eq v_13776 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13760 (isBitSet v_13756 0)) (bit_and v_13759 (eq v_13769 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13760 (eq v_13757 (expression.bv_nat 32 0))) (bit_and v_13759 (eq v_13763 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3114 : Mem) => do
      v_14586 <- evaluateAddress v_3114;
      v_14587 <- load v_14586 4;
      v_14589 <- eval (ashr (concat v_14587 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_14590 <- eval (extract v_14589 0 32);
      store v_14586 v_14590 4;
      setRegister af undef;
      setRegister cf (isBitSet v_14589 32);
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_14589 24 32));
      setRegister sf (isBitSet v_14589 0);
      setRegister zf (zeroFlag v_14590);
      pure ()
    pat_end
