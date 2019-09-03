def salq1 : instruction :=
  definst "salq" $ do
    pattern fun cl (v_2965 : reg (bv 64)) => do
      v_6582 <- getRegister rcx;
      v_6584 <- eval (bv_and (extract v_6582 56 64) (expression.bv_nat 8 63));
      v_6585 <- eval (uge v_6584 (expression.bv_nat 8 64));
      v_6588 <- eval (eq v_6584 (expression.bv_nat 8 0));
      v_6589 <- eval (notBool_ v_6588);
      v_6590 <- getRegister v_2965;
      v_6595 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6590) (uvalueMInt (concat (expression.bv_nat 57 0) v_6584))) 0 65);
      v_6599 <- getRegister cf;
      v_6604 <- eval (bit_or (bit_and v_6585 undef) (bit_and (notBool_ v_6585) (bit_or (bit_and v_6589 (eq (extract v_6595 0 1) (expression.bv_nat 1 1))) (bit_and v_6588 (eq v_6599 (expression.bv_nat 1 1))))));
      v_6607 <- eval (eq (extract v_6595 1 2) (expression.bv_nat 1 1));
      v_6609 <- getRegister sf;
      v_6614 <- eval (extract v_6595 1 65);
      v_6617 <- getRegister zf;
      v_6622 <- eval (bit_and v_6589 undef);
      v_6623 <- getRegister af;
      v_6658 <- getRegister pf;
      v_6663 <- eval (eq v_6584 (expression.bv_nat 8 1));
      v_6668 <- getRegister of;
      setRegister (lhs.of_reg v_2965) v_6614;
      setRegister of (mux (bit_or (bit_and v_6663 (notBool_ (eq v_6604 v_6607))) (bit_and (notBool_ v_6663) (bit_or v_6622 (bit_and v_6588 (eq v_6668 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6589 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6595 64 65) (expression.bv_nat 1 1)) (eq (extract v_6595 63 64) (expression.bv_nat 1 1)))) (eq (extract v_6595 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6595 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6595 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6595 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6595 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6595 57 58) (expression.bv_nat 1 1)))) (bit_and v_6588 (eq v_6658 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6622 (bit_and v_6588 (eq v_6623 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6589 (eq v_6614 (expression.bv_nat 64 0))) (bit_and v_6588 (eq v_6617 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6589 v_6607) (bit_and v_6588 (eq v_6609 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6604 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2968 : imm int) (v_2970 : reg (bv 64)) => do
      v_6683 <- eval (bv_and (handleImmediateWithSignExtend v_2968 8 8) (expression.bv_nat 8 63));
      v_6684 <- eval (uge v_6683 (expression.bv_nat 8 64));
      v_6687 <- eval (eq v_6683 (expression.bv_nat 8 0));
      v_6688 <- eval (notBool_ v_6687);
      v_6689 <- getRegister v_2970;
      v_6694 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6689) (uvalueMInt (concat (expression.bv_nat 57 0) v_6683))) 0 65);
      v_6698 <- getRegister cf;
      v_6703 <- eval (bit_or (bit_and v_6684 undef) (bit_and (notBool_ v_6684) (bit_or (bit_and v_6688 (eq (extract v_6694 0 1) (expression.bv_nat 1 1))) (bit_and v_6687 (eq v_6698 (expression.bv_nat 1 1))))));
      v_6706 <- eval (eq (extract v_6694 1 2) (expression.bv_nat 1 1));
      v_6708 <- getRegister sf;
      v_6713 <- eval (extract v_6694 1 65);
      v_6716 <- getRegister zf;
      v_6721 <- eval (bit_and v_6688 undef);
      v_6722 <- getRegister af;
      v_6757 <- getRegister pf;
      v_6762 <- eval (eq v_6683 (expression.bv_nat 8 1));
      v_6767 <- getRegister of;
      setRegister (lhs.of_reg v_2970) v_6713;
      setRegister of (mux (bit_or (bit_and v_6762 (notBool_ (eq v_6703 v_6706))) (bit_and (notBool_ v_6762) (bit_or v_6721 (bit_and v_6687 (eq v_6767 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6688 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6694 64 65) (expression.bv_nat 1 1)) (eq (extract v_6694 63 64) (expression.bv_nat 1 1)))) (eq (extract v_6694 62 63) (expression.bv_nat 1 1)))) (eq (extract v_6694 61 62) (expression.bv_nat 1 1)))) (eq (extract v_6694 60 61) (expression.bv_nat 1 1)))) (eq (extract v_6694 59 60) (expression.bv_nat 1 1)))) (eq (extract v_6694 58 59) (expression.bv_nat 1 1)))) (eq (extract v_6694 57 58) (expression.bv_nat 1 1)))) (bit_and v_6687 (eq v_6757 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6721 (bit_and v_6687 (eq v_6722 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6688 (eq v_6713 (expression.bv_nat 64 0))) (bit_and v_6687 (eq v_6716 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6688 v_6706) (bit_and v_6687 (eq v_6708 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6703 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2977 : reg (bv 64)) => do
      v_6783 <- getRegister v_2977;
      v_6786 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6783) 1) 0 65);
      v_6787 <- eval (extract v_6786 0 1);
      v_6788 <- eval (extract v_6786 1 2);
      v_6789 <- eval (extract v_6786 1 65);
      setRegister (lhs.of_reg v_2977) v_6789;
      setRegister of (mux (notBool_ (eq (eq v_6787 (expression.bv_nat 1 1)) (eq v_6788 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_6786 57 65));
      setRegister af undef;
      setRegister zf (zeroFlag v_6789);
      setRegister sf v_6788;
      setRegister cf v_6787;
      pure ()
    pat_end;
    pattern fun (v_2973 : reg (bv 64)) => do
      v_9504 <- getRegister v_2973;
      v_9507 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9504) 1) 0 65);
      v_9509 <- eval (eq (extract v_9507 0 1) (expression.bv_nat 1 1));
      v_9512 <- eval (eq (extract v_9507 1 2) (expression.bv_nat 1 1));
      v_9514 <- eval (extract v_9507 1 65);
      setRegister (lhs.of_reg v_2973) v_9514;
      setRegister of (mux (notBool_ (eq v_9509 v_9512)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9507 57 65));
      setRegister zf (zeroFlag v_9514);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux v_9512 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9509 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2973 : reg (bv 64)) => do
      v_9528 <- getRegister v_2973;
      v_9531 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9528) 1) 0 65);
      v_9532 <- eval (extract v_9531 0 1);
      v_9533 <- eval (extract v_9531 1 2);
      v_9534 <- eval (extract v_9531 1 65);
      setRegister (lhs.of_reg v_2973) v_9534;
      setRegister of (mux (notBool_ (eq (eq v_9532 (expression.bv_nat 1 1)) (eq v_9533 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9531 57 65));
      setRegister zf (zeroFlag v_9534);
      setRegister af undef;
      setRegister sf v_9533;
      setRegister cf v_9532;
      pure ()
    pat_end;
    pattern fun cl (v_2951 : Mem) => do
      v_15817 <- evaluateAddress v_2951;
      v_15818 <- load v_15817 8;
      v_15820 <- getRegister rcx;
      v_15822 <- eval (bv_and (extract v_15820 56 64) (expression.bv_nat 8 63));
      v_15826 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_15818) (uvalueMInt (concat (expression.bv_nat 57 0) v_15822))) 0 65);
      v_15827 <- eval (extract v_15826 1 65);
      store v_15817 v_15827 8;
      v_15829 <- eval (uge v_15822 (expression.bv_nat 8 64));
      v_15832 <- eval (eq v_15822 (expression.bv_nat 8 0));
      v_15833 <- eval (notBool_ v_15832);
      v_15837 <- getRegister cf;
      v_15842 <- eval (bit_or (bit_and v_15829 undef) (bit_and (notBool_ v_15829) (bit_or (bit_and v_15833 (eq (extract v_15826 0 1) (expression.bv_nat 1 1))) (bit_and v_15832 (eq v_15837 (expression.bv_nat 1 1))))));
      v_15845 <- eval (eq (extract v_15826 1 2) (expression.bv_nat 1 1));
      v_15847 <- getRegister sf;
      v_15854 <- getRegister zf;
      v_15859 <- eval (bit_and v_15833 undef);
      v_15860 <- getRegister af;
      v_15895 <- getRegister pf;
      v_15900 <- eval (eq v_15822 (expression.bv_nat 8 1));
      v_15905 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15900 (notBool_ (eq v_15842 v_15845))) (bit_and (notBool_ v_15900) (bit_or v_15859 (bit_and v_15832 (eq v_15905 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15833 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15826 64 65) (expression.bv_nat 1 1)) (eq (extract v_15826 63 64) (expression.bv_nat 1 1)))) (eq (extract v_15826 62 63) (expression.bv_nat 1 1)))) (eq (extract v_15826 61 62) (expression.bv_nat 1 1)))) (eq (extract v_15826 60 61) (expression.bv_nat 1 1)))) (eq (extract v_15826 59 60) (expression.bv_nat 1 1)))) (eq (extract v_15826 58 59) (expression.bv_nat 1 1)))) (eq (extract v_15826 57 58) (expression.bv_nat 1 1)))) (bit_and v_15832 (eq v_15895 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15859 (bit_and v_15832 (eq v_15860 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15833 (eq v_15827 (expression.bv_nat 64 0))) (bit_and v_15832 (eq v_15854 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15833 v_15845) (bit_and v_15832 (eq v_15847 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15842 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2955 : imm int) (v_2954 : Mem) => do
      v_15918 <- evaluateAddress v_2954;
      v_15919 <- load v_15918 8;
      v_15922 <- eval (bv_and (handleImmediateWithSignExtend v_2955 8 8) (expression.bv_nat 8 63));
      v_15926 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_15919) (uvalueMInt (concat (expression.bv_nat 57 0) v_15922))) 0 65);
      v_15927 <- eval (extract v_15926 1 65);
      store v_15918 v_15927 8;
      v_15929 <- eval (uge v_15922 (expression.bv_nat 8 64));
      v_15932 <- eval (eq v_15922 (expression.bv_nat 8 0));
      v_15933 <- eval (notBool_ v_15932);
      v_15937 <- getRegister cf;
      v_15942 <- eval (bit_or (bit_and v_15929 undef) (bit_and (notBool_ v_15929) (bit_or (bit_and v_15933 (eq (extract v_15926 0 1) (expression.bv_nat 1 1))) (bit_and v_15932 (eq v_15937 (expression.bv_nat 1 1))))));
      v_15945 <- eval (eq (extract v_15926 1 2) (expression.bv_nat 1 1));
      v_15947 <- getRegister sf;
      v_15954 <- getRegister zf;
      v_15959 <- eval (bit_and v_15933 undef);
      v_15960 <- getRegister af;
      v_15995 <- getRegister pf;
      v_16000 <- eval (eq v_15922 (expression.bv_nat 8 1));
      v_16005 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16000 (notBool_ (eq v_15942 v_15945))) (bit_and (notBool_ v_16000) (bit_or v_15959 (bit_and v_15932 (eq v_16005 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_15933 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_15926 64 65) (expression.bv_nat 1 1)) (eq (extract v_15926 63 64) (expression.bv_nat 1 1)))) (eq (extract v_15926 62 63) (expression.bv_nat 1 1)))) (eq (extract v_15926 61 62) (expression.bv_nat 1 1)))) (eq (extract v_15926 60 61) (expression.bv_nat 1 1)))) (eq (extract v_15926 59 60) (expression.bv_nat 1 1)))) (eq (extract v_15926 58 59) (expression.bv_nat 1 1)))) (eq (extract v_15926 57 58) (expression.bv_nat 1 1)))) (bit_and v_15932 (eq v_15995 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_15959 (bit_and v_15932 (eq v_15960 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_15933 (eq v_15927 (expression.bv_nat 64 0))) (bit_and v_15932 (eq v_15954 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_15933 v_15945) (bit_and v_15932 (eq v_15947 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_15942 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2958 : Mem) => do
      v_18015 <- evaluateAddress v_2958;
      v_18016 <- load v_18015 8;
      v_18019 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_18016) 1) 0 65);
      v_18020 <- eval (extract v_18019 1 65);
      store v_18015 v_18020 8;
      v_18023 <- eval (eq (extract v_18019 0 1) (expression.bv_nat 1 1));
      v_18026 <- eval (eq (extract v_18019 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_18023 v_18026)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18019 57 65));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18020);
      setRegister sf (mux v_18026 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18023 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2958 : Mem) => do
      v_18040 <- evaluateAddress v_2958;
      v_18041 <- load v_18040 8;
      v_18044 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_18041) 1) 0 65);
      v_18045 <- eval (extract v_18044 1 65);
      store v_18040 v_18045 8;
      v_18047 <- eval (extract v_18044 0 1);
      v_18048 <- eval (extract v_18044 1 2);
      setRegister of (mux (notBool_ (eq (eq v_18047 (expression.bv_nat 1 1)) (eq v_18048 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18044 57 65));
      setRegister af undef;
      setRegister zf (zeroFlag v_18045);
      setRegister sf v_18048;
      setRegister cf v_18047;
      pure ()
    pat_end
