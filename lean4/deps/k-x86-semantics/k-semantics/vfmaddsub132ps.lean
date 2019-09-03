def vfmaddsub132ps1 : instruction :=
  definst "vfmaddsub132ps" $ do
    pattern fun (v_2651 : reg (bv 128)) (v_2652 : reg (bv 128)) (v_2653 : reg (bv 128)) => do
      v_5746 <- getRegister v_2653;
      v_5747 <- eval (extract v_5746 0 32);
      v_5755 <- getRegister v_2651;
      v_5756 <- eval (extract v_5755 0 32);
      v_5765 <- getRegister v_2652;
      v_5766 <- eval (extract v_5765 0 32);
      v_5776 <- eval (extract v_5746 32 64);
      v_5784 <- eval (extract v_5755 32 64);
      v_5793 <- eval (extract v_5765 32 64);
      v_5804 <- eval (extract v_5746 64 96);
      v_5812 <- eval (extract v_5755 64 96);
      v_5821 <- eval (extract v_5765 64 96);
      v_5831 <- eval (extract v_5746 96 128);
      v_5839 <- eval (extract v_5755 96 128);
      v_5848 <- eval (extract v_5765 96 128);
      setRegister (lhs.of_reg v_2653) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5747 0 1)) (uvalueMInt (extract v_5747 1 9)) (uvalueMInt (extract v_5747 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5756 0 1)) (uvalueMInt (extract v_5756 1 9)) (uvalueMInt (extract v_5756 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5766 0 1)) (uvalueMInt (extract v_5766 1 9)) (uvalueMInt (extract v_5766 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5776 0 1)) (uvalueMInt (extract v_5776 1 9)) (uvalueMInt (extract v_5776 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5784 0 1)) (uvalueMInt (extract v_5784 1 9)) (uvalueMInt (extract v_5784 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5793 0 1)) (uvalueMInt (extract v_5793 1 9)) (uvalueMInt (extract v_5793 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5804 0 1)) (uvalueMInt (extract v_5804 1 9)) (uvalueMInt (extract v_5804 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5812 0 1)) (uvalueMInt (extract v_5812 1 9)) (uvalueMInt (extract v_5812 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5821 0 1)) (uvalueMInt (extract v_5821 1 9)) (uvalueMInt (extract v_5821 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5831 0 1)) (uvalueMInt (extract v_5831 1 9)) (uvalueMInt (extract v_5831 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5839 0 1)) (uvalueMInt (extract v_5839 1 9)) (uvalueMInt (extract v_5839 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5848 0 1)) (uvalueMInt (extract v_5848 1 9)) (uvalueMInt (extract v_5848 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2662 : reg (bv 256)) (v_2663 : reg (bv 256)) (v_2664 : reg (bv 256)) => do
      v_5866 <- getRegister v_2664;
      v_5867 <- eval (extract v_5866 0 32);
      v_5875 <- getRegister v_2662;
      v_5876 <- eval (extract v_5875 0 32);
      v_5885 <- getRegister v_2663;
      v_5886 <- eval (extract v_5885 0 32);
      v_5896 <- eval (extract v_5866 32 64);
      v_5904 <- eval (extract v_5875 32 64);
      v_5913 <- eval (extract v_5885 32 64);
      v_5924 <- eval (extract v_5866 64 96);
      v_5932 <- eval (extract v_5875 64 96);
      v_5941 <- eval (extract v_5885 64 96);
      v_5951 <- eval (extract v_5866 96 128);
      v_5959 <- eval (extract v_5875 96 128);
      v_5968 <- eval (extract v_5885 96 128);
      v_5979 <- eval (extract v_5866 128 160);
      v_5987 <- eval (extract v_5875 128 160);
      v_5996 <- eval (extract v_5885 128 160);
      v_6006 <- eval (extract v_5866 160 192);
      v_6014 <- eval (extract v_5875 160 192);
      v_6023 <- eval (extract v_5885 160 192);
      v_6034 <- eval (extract v_5866 192 224);
      v_6042 <- eval (extract v_5875 192 224);
      v_6051 <- eval (extract v_5885 192 224);
      v_6061 <- eval (extract v_5866 224 256);
      v_6069 <- eval (extract v_5875 224 256);
      v_6078 <- eval (extract v_5885 224 256);
      setRegister (lhs.of_reg v_2664) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5867 0 1)) (uvalueMInt (extract v_5867 1 9)) (uvalueMInt (extract v_5867 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5876 0 1)) (uvalueMInt (extract v_5876 1 9)) (uvalueMInt (extract v_5876 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5886 0 1)) (uvalueMInt (extract v_5886 1 9)) (uvalueMInt (extract v_5886 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5896 0 1)) (uvalueMInt (extract v_5896 1 9)) (uvalueMInt (extract v_5896 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5904 0 1)) (uvalueMInt (extract v_5904 1 9)) (uvalueMInt (extract v_5904 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5913 0 1)) (uvalueMInt (extract v_5913 1 9)) (uvalueMInt (extract v_5913 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5924 0 1)) (uvalueMInt (extract v_5924 1 9)) (uvalueMInt (extract v_5924 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5932 0 1)) (uvalueMInt (extract v_5932 1 9)) (uvalueMInt (extract v_5932 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5941 0 1)) (uvalueMInt (extract v_5941 1 9)) (uvalueMInt (extract v_5941 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5951 0 1)) (uvalueMInt (extract v_5951 1 9)) (uvalueMInt (extract v_5951 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5959 0 1)) (uvalueMInt (extract v_5959 1 9)) (uvalueMInt (extract v_5959 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5968 0 1)) (uvalueMInt (extract v_5968 1 9)) (uvalueMInt (extract v_5968 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5979 0 1)) (uvalueMInt (extract v_5979 1 9)) (uvalueMInt (extract v_5979 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5987 0 1)) (uvalueMInt (extract v_5987 1 9)) (uvalueMInt (extract v_5987 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5996 0 1)) (uvalueMInt (extract v_5996 1 9)) (uvalueMInt (extract v_5996 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6006 0 1)) (uvalueMInt (extract v_6006 1 9)) (uvalueMInt (extract v_6006 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6014 0 1)) (uvalueMInt (extract v_6014 1 9)) (uvalueMInt (extract v_6014 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6023 0 1)) (uvalueMInt (extract v_6023 1 9)) (uvalueMInt (extract v_6023 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6034 0 1)) (uvalueMInt (extract v_6034 1 9)) (uvalueMInt (extract v_6034 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6042 0 1)) (uvalueMInt (extract v_6042 1 9)) (uvalueMInt (extract v_6042 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6051 0 1)) (uvalueMInt (extract v_6051 1 9)) (uvalueMInt (extract v_6051 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6061 0 1)) (uvalueMInt (extract v_6061 1 9)) (uvalueMInt (extract v_6061 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6069 0 1)) (uvalueMInt (extract v_6069 1 9)) (uvalueMInt (extract v_6069 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6078 0 1)) (uvalueMInt (extract v_6078 1 9)) (uvalueMInt (extract v_6078 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2648 : Mem) (v_2646 : reg (bv 128)) (v_2647 : reg (bv 128)) => do
      v_16609 <- getRegister v_2647;
      v_16610 <- eval (extract v_16609 0 32);
      v_16618 <- evaluateAddress v_2648;
      v_16619 <- load v_16618 16;
      v_16620 <- eval (extract v_16619 0 32);
      v_16629 <- getRegister v_2646;
      v_16630 <- eval (extract v_16629 0 32);
      v_16640 <- eval (extract v_16609 32 64);
      v_16648 <- eval (extract v_16619 32 64);
      v_16657 <- eval (extract v_16629 32 64);
      v_16668 <- eval (extract v_16609 64 96);
      v_16676 <- eval (extract v_16619 64 96);
      v_16685 <- eval (extract v_16629 64 96);
      v_16695 <- eval (extract v_16609 96 128);
      v_16703 <- eval (extract v_16619 96 128);
      v_16712 <- eval (extract v_16629 96 128);
      setRegister (lhs.of_reg v_2647) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16610 0 1)) (uvalueMInt (extract v_16610 1 9)) (uvalueMInt (extract v_16610 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16620 0 1)) (uvalueMInt (extract v_16620 1 9)) (uvalueMInt (extract v_16620 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16630 0 1)) (uvalueMInt (extract v_16630 1 9)) (uvalueMInt (extract v_16630 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16640 0 1)) (uvalueMInt (extract v_16640 1 9)) (uvalueMInt (extract v_16640 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16648 0 1)) (uvalueMInt (extract v_16648 1 9)) (uvalueMInt (extract v_16648 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16657 0 1)) (uvalueMInt (extract v_16657 1 9)) (uvalueMInt (extract v_16657 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16668 0 1)) (uvalueMInt (extract v_16668 1 9)) (uvalueMInt (extract v_16668 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16676 0 1)) (uvalueMInt (extract v_16676 1 9)) (uvalueMInt (extract v_16676 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16685 0 1)) (uvalueMInt (extract v_16685 1 9)) (uvalueMInt (extract v_16685 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16695 0 1)) (uvalueMInt (extract v_16695 1 9)) (uvalueMInt (extract v_16695 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16703 0 1)) (uvalueMInt (extract v_16703 1 9)) (uvalueMInt (extract v_16703 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16712 0 1)) (uvalueMInt (extract v_16712 1 9)) (uvalueMInt (extract v_16712 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2657 : Mem) (v_2658 : reg (bv 256)) (v_2659 : reg (bv 256)) => do
      v_16725 <- getRegister v_2659;
      v_16726 <- eval (extract v_16725 0 32);
      v_16734 <- evaluateAddress v_2657;
      v_16735 <- load v_16734 32;
      v_16736 <- eval (extract v_16735 0 32);
      v_16745 <- getRegister v_2658;
      v_16746 <- eval (extract v_16745 0 32);
      v_16756 <- eval (extract v_16725 32 64);
      v_16764 <- eval (extract v_16735 32 64);
      v_16773 <- eval (extract v_16745 32 64);
      v_16784 <- eval (extract v_16725 64 96);
      v_16792 <- eval (extract v_16735 64 96);
      v_16801 <- eval (extract v_16745 64 96);
      v_16811 <- eval (extract v_16725 96 128);
      v_16819 <- eval (extract v_16735 96 128);
      v_16828 <- eval (extract v_16745 96 128);
      v_16839 <- eval (extract v_16725 128 160);
      v_16847 <- eval (extract v_16735 128 160);
      v_16856 <- eval (extract v_16745 128 160);
      v_16866 <- eval (extract v_16725 160 192);
      v_16874 <- eval (extract v_16735 160 192);
      v_16883 <- eval (extract v_16745 160 192);
      v_16894 <- eval (extract v_16725 192 224);
      v_16902 <- eval (extract v_16735 192 224);
      v_16911 <- eval (extract v_16745 192 224);
      v_16921 <- eval (extract v_16725 224 256);
      v_16929 <- eval (extract v_16735 224 256);
      v_16938 <- eval (extract v_16745 224 256);
      setRegister (lhs.of_reg v_2659) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16726 0 1)) (uvalueMInt (extract v_16726 1 9)) (uvalueMInt (extract v_16726 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16736 0 1)) (uvalueMInt (extract v_16736 1 9)) (uvalueMInt (extract v_16736 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16746 0 1)) (uvalueMInt (extract v_16746 1 9)) (uvalueMInt (extract v_16746 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16756 0 1)) (uvalueMInt (extract v_16756 1 9)) (uvalueMInt (extract v_16756 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16764 0 1)) (uvalueMInt (extract v_16764 1 9)) (uvalueMInt (extract v_16764 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16773 0 1)) (uvalueMInt (extract v_16773 1 9)) (uvalueMInt (extract v_16773 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16784 0 1)) (uvalueMInt (extract v_16784 1 9)) (uvalueMInt (extract v_16784 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16792 0 1)) (uvalueMInt (extract v_16792 1 9)) (uvalueMInt (extract v_16792 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16801 0 1)) (uvalueMInt (extract v_16801 1 9)) (uvalueMInt (extract v_16801 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16811 0 1)) (uvalueMInt (extract v_16811 1 9)) (uvalueMInt (extract v_16811 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16819 0 1)) (uvalueMInt (extract v_16819 1 9)) (uvalueMInt (extract v_16819 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16828 0 1)) (uvalueMInt (extract v_16828 1 9)) (uvalueMInt (extract v_16828 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16839 0 1)) (uvalueMInt (extract v_16839 1 9)) (uvalueMInt (extract v_16839 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16847 0 1)) (uvalueMInt (extract v_16847 1 9)) (uvalueMInt (extract v_16847 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16856 0 1)) (uvalueMInt (extract v_16856 1 9)) (uvalueMInt (extract v_16856 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16866 0 1)) (uvalueMInt (extract v_16866 1 9)) (uvalueMInt (extract v_16866 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16874 0 1)) (uvalueMInt (extract v_16874 1 9)) (uvalueMInt (extract v_16874 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16883 0 1)) (uvalueMInt (extract v_16883 1 9)) (uvalueMInt (extract v_16883 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16894 0 1)) (uvalueMInt (extract v_16894 1 9)) (uvalueMInt (extract v_16894 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16902 0 1)) (uvalueMInt (extract v_16902 1 9)) (uvalueMInt (extract v_16902 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16911 0 1)) (uvalueMInt (extract v_16911 1 9)) (uvalueMInt (extract v_16911 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16921 0 1)) (uvalueMInt (extract v_16921 1 9)) (uvalueMInt (extract v_16921 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16929 0 1)) (uvalueMInt (extract v_16929 1 9)) (uvalueMInt (extract v_16929 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16938 0 1)) (uvalueMInt (extract v_16938 1 9)) (uvalueMInt (extract v_16938 9 32)))) 32)))));
      pure ()
    pat_end
