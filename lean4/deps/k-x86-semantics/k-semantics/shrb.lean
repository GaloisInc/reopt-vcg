def shrb1 : instruction :=
  definst "shrb" $ do
    pattern fun cl (v_2870 : reg (bv 8)) => do
      v_5496 <- getRegister rcx;
      v_5498 <- eval (bv_and (extract v_5496 56 64) (expression.bv_nat 8 31));
      v_5499 <- eval (uge v_5498 (expression.bv_nat 8 8));
      v_5502 <- eval (eq v_5498 (expression.bv_nat 8 0));
      v_5503 <- eval (notBool_ v_5502);
      v_5504 <- getRegister v_2870;
      v_5508 <- eval (lshr (concat v_5504 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_5498)));
      v_5512 <- getRegister cf;
      v_5520 <- eval (eq (extract v_5508 0 1) (expression.bv_nat 1 1));
      v_5522 <- getRegister sf;
      v_5527 <- eval (extract v_5508 0 8);
      v_5530 <- getRegister zf;
      v_5535 <- eval (bit_and v_5503 undef);
      v_5536 <- getRegister af;
      v_5569 <- getRegister pf;
      v_5574 <- eval (eq v_5498 (expression.bv_nat 8 1));
      v_5579 <- getRegister of;
      setRegister (lhs.of_reg v_2870) v_5527;
      setRegister of (mux (bit_or (bit_and v_5574 (eq (extract v_5504 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_5574) (bit_or v_5535 (bit_and v_5502 (eq v_5579 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5503 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5508 7 8) (expression.bv_nat 1 1)) (eq (extract v_5508 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5508 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5508 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5508 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5508 2 3) (expression.bv_nat 1 1)))) (eq (extract v_5508 1 2) (expression.bv_nat 1 1)))) v_5520)) (bit_and v_5502 (eq v_5569 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5535 (bit_and v_5502 (eq v_5536 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5503 (eq v_5527 (expression.bv_nat 8 0))) (bit_and v_5502 (eq v_5530 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5503 v_5520) (bit_and v_5502 (eq v_5522 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5499 undef) (bit_and (notBool_ v_5499) (bit_or (bit_and v_5503 (eq (extract v_5508 8 9) (expression.bv_nat 1 1))) (bit_and v_5502 (eq v_5512 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2873 : imm int) (v_2875 : reg (bv 8)) => do
      v_5594 <- eval (bv_and (handleImmediateWithSignExtend v_2873 8 8) (expression.bv_nat 8 31));
      v_5595 <- eval (uge v_5594 (expression.bv_nat 8 8));
      v_5598 <- eval (eq v_5594 (expression.bv_nat 8 0));
      v_5599 <- eval (notBool_ v_5598);
      v_5600 <- getRegister v_2875;
      v_5604 <- eval (lshr (concat v_5600 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_5594)));
      v_5608 <- getRegister cf;
      v_5616 <- eval (eq (extract v_5604 0 1) (expression.bv_nat 1 1));
      v_5618 <- getRegister sf;
      v_5623 <- eval (extract v_5604 0 8);
      v_5626 <- getRegister zf;
      v_5631 <- eval (bit_and v_5599 undef);
      v_5632 <- getRegister af;
      v_5665 <- getRegister pf;
      v_5670 <- eval (eq v_5594 (expression.bv_nat 8 1));
      v_5675 <- getRegister of;
      setRegister (lhs.of_reg v_2875) v_5623;
      setRegister of (mux (bit_or (bit_and v_5670 (eq (extract v_5600 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_5670) (bit_or v_5631 (bit_and v_5598 (eq v_5675 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5599 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5604 7 8) (expression.bv_nat 1 1)) (eq (extract v_5604 6 7) (expression.bv_nat 1 1)))) (eq (extract v_5604 5 6) (expression.bv_nat 1 1)))) (eq (extract v_5604 4 5) (expression.bv_nat 1 1)))) (eq (extract v_5604 3 4) (expression.bv_nat 1 1)))) (eq (extract v_5604 2 3) (expression.bv_nat 1 1)))) (eq (extract v_5604 1 2) (expression.bv_nat 1 1)))) v_5616)) (bit_and v_5598 (eq v_5665 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5631 (bit_and v_5598 (eq v_5632 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5599 (eq v_5623 (expression.bv_nat 8 0))) (bit_and v_5598 (eq v_5626 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5599 v_5616) (bit_and v_5598 (eq v_5618 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5595 undef) (bit_and (notBool_ v_5595) (bit_or (bit_and v_5599 (eq (extract v_5604 8 9) (expression.bv_nat 1 1))) (bit_and v_5598 (eq v_5608 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2882 : reg (bv 8)) => do
      v_5691 <- getRegister v_2882;
      v_5693 <- eval (lshr (concat v_5691 (expression.bv_nat 1 0)) 1);
      v_5696 <- eval (extract v_5693 0 8);
      setRegister (lhs.of_reg v_2882) v_5696;
      setRegister of (extract v_5691 0 1);
      setRegister pf (parityFlag v_5696);
      setRegister af undef;
      setRegister zf (zeroFlag v_5696);
      setRegister sf (extract v_5693 0 1);
      setRegister cf (extract v_5693 8 9);
      pure ()
    pat_end;
    pattern fun (v_2878 : reg (bv 8)) => do
      v_7872 <- getRegister v_2878;
      v_7874 <- eval (lshr (concat v_7872 (expression.bv_nat 1 0)) 1);
      v_7881 <- eval (extract v_7874 0 8);
      setRegister (lhs.of_reg v_2878) v_7881;
      setRegister of (mux (eq (extract v_7872 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_7881);
      setRegister zf (zeroFlag v_7881);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_7874 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_7874 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2878 : reg (bv 8)) => do
      v_7894 <- getRegister v_2878;
      v_7896 <- eval (lshr (concat v_7894 (expression.bv_nat 1 0)) 1);
      v_7899 <- eval (extract v_7896 0 8);
      setRegister (lhs.of_reg v_2878) v_7899;
      setRegister of (extract v_7894 0 1);
      setRegister pf (parityFlag v_7899);
      setRegister zf (zeroFlag v_7899);
      setRegister af undef;
      setRegister sf (extract v_7896 0 1);
      setRegister cf (extract v_7896 8 9);
      pure ()
    pat_end;
    pattern fun (v_2894 : reg (bv 8)) => do
      v_7910 <- getRegister v_2894;
      v_7912 <- eval (lshr (concat v_7910 (expression.bv_nat 1 0)) 1);
      v_7919 <- eval (extract v_7912 0 8);
      setRegister (lhs.of_reg v_2894) v_7919;
      setRegister of (mux (eq (extract v_7910 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_7919);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_7919);
      setRegister sf (mux (eq (extract v_7912 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_7912 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2894 : reg (bv 8)) => do
      v_7932 <- getRegister v_2894;
      v_7934 <- eval (lshr (concat v_7932 (expression.bv_nat 1 0)) 1);
      v_7937 <- eval (extract v_7934 0 8);
      setRegister (lhs.of_reg v_2894) v_7937;
      setRegister of (extract v_7932 0 1);
      setRegister pf (parityFlag v_7937);
      setRegister af undef;
      setRegister zf (zeroFlag v_7937);
      setRegister sf (extract v_7934 0 1);
      setRegister cf (extract v_7934 8 9);
      pure ()
    pat_end;
    pattern fun cl (v_2856 : Mem) => do
      v_11799 <- evaluateAddress v_2856;
      v_11800 <- load v_11799 1;
      v_11802 <- getRegister rcx;
      v_11804 <- eval (bv_and (extract v_11802 56 64) (expression.bv_nat 8 31));
      v_11807 <- eval (lshr (concat v_11800 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_11804)));
      v_11808 <- eval (extract v_11807 0 8);
      store v_11799 v_11808 1;
      v_11810 <- eval (uge v_11804 (expression.bv_nat 8 8));
      v_11813 <- eval (eq v_11804 (expression.bv_nat 8 0));
      v_11814 <- eval (notBool_ v_11813);
      v_11818 <- getRegister cf;
      v_11826 <- eval (eq (extract v_11807 0 1) (expression.bv_nat 1 1));
      v_11828 <- getRegister sf;
      v_11835 <- getRegister zf;
      v_11840 <- eval (bit_and v_11814 undef);
      v_11841 <- getRegister af;
      v_11874 <- getRegister pf;
      v_11879 <- eval (eq v_11804 (expression.bv_nat 8 1));
      v_11884 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11879 (eq (extract v_11800 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_11879) (bit_or v_11840 (bit_and v_11813 (eq v_11884 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11814 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11807 7 8) (expression.bv_nat 1 1)) (eq (extract v_11807 6 7) (expression.bv_nat 1 1)))) (eq (extract v_11807 5 6) (expression.bv_nat 1 1)))) (eq (extract v_11807 4 5) (expression.bv_nat 1 1)))) (eq (extract v_11807 3 4) (expression.bv_nat 1 1)))) (eq (extract v_11807 2 3) (expression.bv_nat 1 1)))) (eq (extract v_11807 1 2) (expression.bv_nat 1 1)))) v_11826)) (bit_and v_11813 (eq v_11874 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11840 (bit_and v_11813 (eq v_11841 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11814 (eq v_11808 (expression.bv_nat 8 0))) (bit_and v_11813 (eq v_11835 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11814 v_11826) (bit_and v_11813 (eq v_11828 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_11810 undef) (bit_and (notBool_ v_11810) (bit_or (bit_and v_11814 (eq (extract v_11807 8 9) (expression.bv_nat 1 1))) (bit_and v_11813 (eq v_11818 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2859 : imm int) (v_2860 : Mem) => do
      v_11897 <- evaluateAddress v_2860;
      v_11898 <- load v_11897 1;
      v_11901 <- eval (bv_and (handleImmediateWithSignExtend v_2859 8 8) (expression.bv_nat 8 31));
      v_11904 <- eval (lshr (concat v_11898 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 1 0) v_11901)));
      v_11905 <- eval (extract v_11904 0 8);
      store v_11897 v_11905 1;
      v_11907 <- eval (uge v_11901 (expression.bv_nat 8 8));
      v_11910 <- eval (eq v_11901 (expression.bv_nat 8 0));
      v_11911 <- eval (notBool_ v_11910);
      v_11915 <- getRegister cf;
      v_11923 <- eval (eq (extract v_11904 0 1) (expression.bv_nat 1 1));
      v_11925 <- getRegister sf;
      v_11932 <- getRegister zf;
      v_11937 <- eval (bit_and v_11911 undef);
      v_11938 <- getRegister af;
      v_11971 <- getRegister pf;
      v_11976 <- eval (eq v_11901 (expression.bv_nat 8 1));
      v_11981 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_11976 (eq (extract v_11898 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_11976) (bit_or v_11937 (bit_and v_11910 (eq v_11981 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_11911 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_11904 7 8) (expression.bv_nat 1 1)) (eq (extract v_11904 6 7) (expression.bv_nat 1 1)))) (eq (extract v_11904 5 6) (expression.bv_nat 1 1)))) (eq (extract v_11904 4 5) (expression.bv_nat 1 1)))) (eq (extract v_11904 3 4) (expression.bv_nat 1 1)))) (eq (extract v_11904 2 3) (expression.bv_nat 1 1)))) (eq (extract v_11904 1 2) (expression.bv_nat 1 1)))) v_11923)) (bit_and v_11910 (eq v_11971 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_11937 (bit_and v_11910 (eq v_11938 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_11911 (eq v_11905 (expression.bv_nat 8 0))) (bit_and v_11910 (eq v_11932 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_11911 v_11923) (bit_and v_11910 (eq v_11925 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_11907 undef) (bit_and (notBool_ v_11907) (bit_or (bit_and v_11911 (eq (extract v_11904 8 9) (expression.bv_nat 1 1))) (bit_and v_11910 (eq v_11915 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2863 : Mem) => do
      v_13336 <- evaluateAddress v_2863;
      v_13337 <- load v_13336 1;
      v_13339 <- eval (lshr (concat v_13337 (expression.bv_nat 1 0)) 1);
      v_13340 <- eval (extract v_13339 0 8);
      store v_13336 v_13340 1;
      setRegister of (mux (eq (extract v_13337 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13340);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13340);
      setRegister sf (mux (eq (extract v_13339 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13339 8 9) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2863 : Mem) => do
      v_13359 <- evaluateAddress v_2863;
      v_13360 <- load v_13359 1;
      v_13362 <- eval (lshr (concat v_13360 (expression.bv_nat 1 0)) 1);
      v_13363 <- eval (extract v_13362 0 8);
      store v_13359 v_13363 1;
      setRegister of (extract v_13360 0 1);
      setRegister pf (parityFlag v_13363);
      setRegister af undef;
      setRegister zf (zeroFlag v_13363);
      setRegister sf (extract v_13362 0 1);
      setRegister cf (extract v_13362 8 9);
      pure ()
    pat_end
