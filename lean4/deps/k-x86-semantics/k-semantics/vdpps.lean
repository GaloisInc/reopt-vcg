def vdpps1 : instruction :=
  definst "vdpps" $ do
    pattern fun (v_3437 : imm int) (v_3441 : reg (bv 128)) (v_3442 : reg (bv 128)) (v_3443 : reg (bv 128)) => do
      v_7604 <- eval (handleImmediateWithSignExtend v_3437 8 8);
      v_7609 <- getRegister v_3442;
      v_7610 <- eval (extract v_7609 96 128);
      v_7618 <- getRegister v_3441;
      v_7619 <- eval (extract v_7618 96 128);
      v_7633 <- eval (extract v_7609 64 96);
      v_7641 <- eval (extract v_7618 64 96);
      v_7658 <- eval (extract v_7609 32 64);
      v_7666 <- eval (extract v_7618 32 64);
      v_7680 <- eval (extract v_7609 0 32);
      v_7688 <- eval (extract v_7618 0 32);
      v_7704 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_7604 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7610 0 1)) (uvalueMInt (extract v_7610 1 9)) (uvalueMInt (extract v_7610 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7619 0 1)) (uvalueMInt (extract v_7619 1 9)) (uvalueMInt (extract v_7619 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_7604 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7633 0 1)) (uvalueMInt (extract v_7633 1 9)) (uvalueMInt (extract v_7633 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7641 0 1)) (uvalueMInt (extract v_7641 1 9)) (uvalueMInt (extract v_7641 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_7604 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7658 0 1)) (uvalueMInt (extract v_7658 1 9)) (uvalueMInt (extract v_7658 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7666 0 1)) (uvalueMInt (extract v_7666 1 9)) (uvalueMInt (extract v_7666 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_7604 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7680 0 1)) (uvalueMInt (extract v_7680 1 9)) (uvalueMInt (extract v_7680 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7688 0 1)) (uvalueMInt (extract v_7688 1 9)) (uvalueMInt (extract v_7688 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3443) (concat (concat (concat (mux (eq (extract v_7604 4 5) (expression.bv_nat 1 1)) v_7704 (expression.bv_nat 32 0)) (mux (eq (extract v_7604 5 6) (expression.bv_nat 1 1)) v_7704 (expression.bv_nat 32 0))) (mux (eq (extract v_7604 6 7) (expression.bv_nat 1 1)) v_7704 (expression.bv_nat 32 0))) (mux (eq (extract v_7604 7 8) (expression.bv_nat 1 1)) v_7704 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3450 : imm int) (v_3451 : reg (bv 256)) (v_3452 : reg (bv 256)) (v_3453 : reg (bv 256)) => do
      v_7725 <- eval (handleImmediateWithSignExtend v_3450 8 8);
      v_7727 <- eval (eq (extract v_7725 4 5) (expression.bv_nat 1 1));
      v_7729 <- eval (eq (extract v_7725 3 4) (expression.bv_nat 1 1));
      v_7730 <- getRegister v_3452;
      v_7731 <- eval (extract v_7730 96 128);
      v_7739 <- getRegister v_3451;
      v_7740 <- eval (extract v_7739 96 128);
      v_7753 <- eval (eq (extract v_7725 2 3) (expression.bv_nat 1 1));
      v_7754 <- eval (extract v_7730 64 96);
      v_7762 <- eval (extract v_7739 64 96);
      v_7778 <- eval (eq (extract v_7725 1 2) (expression.bv_nat 1 1));
      v_7779 <- eval (extract v_7730 32 64);
      v_7787 <- eval (extract v_7739 32 64);
      v_7800 <- eval (eq (extract v_7725 0 1) (expression.bv_nat 1 1));
      v_7801 <- eval (extract v_7730 0 32);
      v_7809 <- eval (extract v_7739 0 32);
      v_7825 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_7729 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7731 0 1)) (uvalueMInt (extract v_7731 1 9)) (uvalueMInt (extract v_7731 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7740 0 1)) (uvalueMInt (extract v_7740 1 9)) (uvalueMInt (extract v_7740 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_7753 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7754 0 1)) (uvalueMInt (extract v_7754 1 9)) (uvalueMInt (extract v_7754 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7762 0 1)) (uvalueMInt (extract v_7762 1 9)) (uvalueMInt (extract v_7762 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_7778 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7779 0 1)) (uvalueMInt (extract v_7779 1 9)) (uvalueMInt (extract v_7779 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7787 0 1)) (uvalueMInt (extract v_7787 1 9)) (uvalueMInt (extract v_7787 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_7800 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7801 0 1)) (uvalueMInt (extract v_7801 1 9)) (uvalueMInt (extract v_7801 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7809 0 1)) (uvalueMInt (extract v_7809 1 9)) (uvalueMInt (extract v_7809 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_7828 <- eval (eq (extract v_7725 5 6) (expression.bv_nat 1 1));
      v_7832 <- eval (eq (extract v_7725 6 7) (expression.bv_nat 1 1));
      v_7836 <- eval (eq (extract v_7725 7 8) (expression.bv_nat 1 1));
      v_7839 <- eval (extract v_7730 224 256);
      v_7847 <- eval (extract v_7739 224 256);
      v_7859 <- eval (extract v_7730 192 224);
      v_7867 <- eval (extract v_7739 192 224);
      v_7882 <- eval (extract v_7730 160 192);
      v_7890 <- eval (extract v_7739 160 192);
      v_7902 <- eval (extract v_7730 128 160);
      v_7910 <- eval (extract v_7739 128 160);
      v_7926 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_7729 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7839 0 1)) (uvalueMInt (extract v_7839 1 9)) (uvalueMInt (extract v_7839 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7847 0 1)) (uvalueMInt (extract v_7847 1 9)) (uvalueMInt (extract v_7847 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_7753 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7859 0 1)) (uvalueMInt (extract v_7859 1 9)) (uvalueMInt (extract v_7859 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7867 0 1)) (uvalueMInt (extract v_7867 1 9)) (uvalueMInt (extract v_7867 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_7778 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7882 0 1)) (uvalueMInt (extract v_7882 1 9)) (uvalueMInt (extract v_7882 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7890 0 1)) (uvalueMInt (extract v_7890 1 9)) (uvalueMInt (extract v_7890 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_7800 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7902 0 1)) (uvalueMInt (extract v_7902 1 9)) (uvalueMInt (extract v_7902 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7910 0 1)) (uvalueMInt (extract v_7910 1 9)) (uvalueMInt (extract v_7910 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3453) (concat (concat (concat (concat (mux v_7727 v_7825 (expression.bv_nat 32 0)) (mux v_7828 v_7825 (expression.bv_nat 32 0))) (mux v_7832 v_7825 (expression.bv_nat 32 0))) (mux v_7836 v_7825 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_7727 v_7926 (expression.bv_nat 32 0)) (mux v_7828 v_7926 (expression.bv_nat 32 0))) (mux v_7832 v_7926 (expression.bv_nat 32 0))) (mux v_7836 v_7926 (expression.bv_nat 32 0))));
      pure ()
    pat_end;
    pattern fun (v_3432 : imm int) (v_3431 : Mem) (v_3435 : reg (bv 128)) (v_3436 : reg (bv 128)) => do
      v_12791 <- eval (handleImmediateWithSignExtend v_3432 8 8);
      v_12796 <- getRegister v_3435;
      v_12797 <- eval (extract v_12796 96 128);
      v_12805 <- evaluateAddress v_3431;
      v_12806 <- load v_12805 16;
      v_12807 <- eval (extract v_12806 96 128);
      v_12821 <- eval (extract v_12796 64 96);
      v_12829 <- eval (extract v_12806 64 96);
      v_12846 <- eval (extract v_12796 32 64);
      v_12854 <- eval (extract v_12806 32 64);
      v_12868 <- eval (extract v_12796 0 32);
      v_12876 <- eval (extract v_12806 0 32);
      v_12892 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_12791 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12797 0 1)) (uvalueMInt (extract v_12797 1 9)) (uvalueMInt (extract v_12797 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12807 0 1)) (uvalueMInt (extract v_12807 1 9)) (uvalueMInt (extract v_12807 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_12791 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12821 0 1)) (uvalueMInt (extract v_12821 1 9)) (uvalueMInt (extract v_12821 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12829 0 1)) (uvalueMInt (extract v_12829 1 9)) (uvalueMInt (extract v_12829 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_12791 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12846 0 1)) (uvalueMInt (extract v_12846 1 9)) (uvalueMInt (extract v_12846 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12854 0 1)) (uvalueMInt (extract v_12854 1 9)) (uvalueMInt (extract v_12854 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_12791 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12868 0 1)) (uvalueMInt (extract v_12868 1 9)) (uvalueMInt (extract v_12868 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12876 0 1)) (uvalueMInt (extract v_12876 1 9)) (uvalueMInt (extract v_12876 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3436) (concat (concat (concat (mux (eq (extract v_12791 4 5) (expression.bv_nat 1 1)) v_12892 (expression.bv_nat 32 0)) (mux (eq (extract v_12791 5 6) (expression.bv_nat 1 1)) v_12892 (expression.bv_nat 32 0))) (mux (eq (extract v_12791 6 7) (expression.bv_nat 1 1)) v_12892 (expression.bv_nat 32 0))) (mux (eq (extract v_12791 7 8) (expression.bv_nat 1 1)) v_12892 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3445 : imm int) (v_3444 : Mem) (v_3446 : reg (bv 256)) (v_3447 : reg (bv 256)) => do
      v_12907 <- eval (handleImmediateWithSignExtend v_3445 8 8);
      v_12909 <- eval (eq (extract v_12907 4 5) (expression.bv_nat 1 1));
      v_12911 <- eval (eq (extract v_12907 3 4) (expression.bv_nat 1 1));
      v_12912 <- getRegister v_3446;
      v_12913 <- eval (extract v_12912 96 128);
      v_12921 <- evaluateAddress v_3444;
      v_12922 <- load v_12921 32;
      v_12923 <- eval (extract v_12922 96 128);
      v_12936 <- eval (eq (extract v_12907 2 3) (expression.bv_nat 1 1));
      v_12937 <- eval (extract v_12912 64 96);
      v_12945 <- eval (extract v_12922 64 96);
      v_12961 <- eval (eq (extract v_12907 1 2) (expression.bv_nat 1 1));
      v_12962 <- eval (extract v_12912 32 64);
      v_12970 <- eval (extract v_12922 32 64);
      v_12983 <- eval (eq (extract v_12907 0 1) (expression.bv_nat 1 1));
      v_12984 <- eval (extract v_12912 0 32);
      v_12992 <- eval (extract v_12922 0 32);
      v_13008 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_12911 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12913 0 1)) (uvalueMInt (extract v_12913 1 9)) (uvalueMInt (extract v_12913 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12923 0 1)) (uvalueMInt (extract v_12923 1 9)) (uvalueMInt (extract v_12923 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_12936 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12937 0 1)) (uvalueMInt (extract v_12937 1 9)) (uvalueMInt (extract v_12937 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12945 0 1)) (uvalueMInt (extract v_12945 1 9)) (uvalueMInt (extract v_12945 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_12961 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12962 0 1)) (uvalueMInt (extract v_12962 1 9)) (uvalueMInt (extract v_12962 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12970 0 1)) (uvalueMInt (extract v_12970 1 9)) (uvalueMInt (extract v_12970 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_12983 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12984 0 1)) (uvalueMInt (extract v_12984 1 9)) (uvalueMInt (extract v_12984 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12992 0 1)) (uvalueMInt (extract v_12992 1 9)) (uvalueMInt (extract v_12992 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_13011 <- eval (eq (extract v_12907 5 6) (expression.bv_nat 1 1));
      v_13015 <- eval (eq (extract v_12907 6 7) (expression.bv_nat 1 1));
      v_13019 <- eval (eq (extract v_12907 7 8) (expression.bv_nat 1 1));
      v_13022 <- eval (extract v_12912 224 256);
      v_13030 <- eval (extract v_12922 224 256);
      v_13042 <- eval (extract v_12912 192 224);
      v_13050 <- eval (extract v_12922 192 224);
      v_13065 <- eval (extract v_12912 160 192);
      v_13073 <- eval (extract v_12922 160 192);
      v_13085 <- eval (extract v_12912 128 160);
      v_13093 <- eval (extract v_12922 128 160);
      v_13109 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_12911 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13022 0 1)) (uvalueMInt (extract v_13022 1 9)) (uvalueMInt (extract v_13022 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13030 0 1)) (uvalueMInt (extract v_13030 1 9)) (uvalueMInt (extract v_13030 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_12936 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13042 0 1)) (uvalueMInt (extract v_13042 1 9)) (uvalueMInt (extract v_13042 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13050 0 1)) (uvalueMInt (extract v_13050 1 9)) (uvalueMInt (extract v_13050 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_12961 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13065 0 1)) (uvalueMInt (extract v_13065 1 9)) (uvalueMInt (extract v_13065 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13073 0 1)) (uvalueMInt (extract v_13073 1 9)) (uvalueMInt (extract v_13073 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_12983 (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13085 0 1)) (uvalueMInt (extract v_13085 1 9)) (uvalueMInt (extract v_13085 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_13093 0 1)) (uvalueMInt (extract v_13093 1 9)) (uvalueMInt (extract v_13093 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3447) (concat (concat (concat (concat (mux v_12909 v_13008 (expression.bv_nat 32 0)) (mux v_13011 v_13008 (expression.bv_nat 32 0))) (mux v_13015 v_13008 (expression.bv_nat 32 0))) (mux v_13019 v_13008 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_12909 v_13109 (expression.bv_nat 32 0)) (mux v_13011 v_13109 (expression.bv_nat 32 0))) (mux v_13015 v_13109 (expression.bv_nat 32 0))) (mux v_13019 v_13109 (expression.bv_nat 32 0))));
      pure ()
    pat_end
