def vfmaddsub231ps1 : instruction :=
  definst "vfmaddsub231ps" $ do
    pattern fun (v_2739 : reg (bv 128)) (v_2740 : reg (bv 128)) (v_2741 : reg (bv 128)) => do
      v_6818 <- getRegister v_2740;
      v_6819 <- eval (extract v_6818 0 32);
      v_6827 <- getRegister v_2739;
      v_6828 <- eval (extract v_6827 0 32);
      v_6837 <- getRegister v_2741;
      v_6838 <- eval (extract v_6837 0 32);
      v_6848 <- eval (extract v_6818 32 64);
      v_6856 <- eval (extract v_6827 32 64);
      v_6865 <- eval (extract v_6837 32 64);
      v_6876 <- eval (extract v_6818 64 96);
      v_6884 <- eval (extract v_6827 64 96);
      v_6893 <- eval (extract v_6837 64 96);
      v_6903 <- eval (extract v_6818 96 128);
      v_6911 <- eval (extract v_6827 96 128);
      v_6920 <- eval (extract v_6837 96 128);
      setRegister (lhs.of_reg v_2741) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6819 0 1)) (uvalueMInt (extract v_6819 1 9)) (uvalueMInt (extract v_6819 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6828 0 1)) (uvalueMInt (extract v_6828 1 9)) (uvalueMInt (extract v_6828 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6838 0 1)) (uvalueMInt (extract v_6838 1 9)) (uvalueMInt (extract v_6838 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6848 0 1)) (uvalueMInt (extract v_6848 1 9)) (uvalueMInt (extract v_6848 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6856 0 1)) (uvalueMInt (extract v_6856 1 9)) (uvalueMInt (extract v_6856 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6865 0 1)) (uvalueMInt (extract v_6865 1 9)) (uvalueMInt (extract v_6865 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6876 0 1)) (uvalueMInt (extract v_6876 1 9)) (uvalueMInt (extract v_6876 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6884 0 1)) (uvalueMInt (extract v_6884 1 9)) (uvalueMInt (extract v_6884 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6893 0 1)) (uvalueMInt (extract v_6893 1 9)) (uvalueMInt (extract v_6893 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6903 0 1)) (uvalueMInt (extract v_6903 1 9)) (uvalueMInt (extract v_6903 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6911 0 1)) (uvalueMInt (extract v_6911 1 9)) (uvalueMInt (extract v_6911 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6920 0 1)) (uvalueMInt (extract v_6920 1 9)) (uvalueMInt (extract v_6920 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2750 : reg (bv 256)) (v_2751 : reg (bv 256)) (v_2752 : reg (bv 256)) => do
      v_6938 <- getRegister v_2751;
      v_6939 <- eval (extract v_6938 0 32);
      v_6947 <- getRegister v_2750;
      v_6948 <- eval (extract v_6947 0 32);
      v_6957 <- getRegister v_2752;
      v_6958 <- eval (extract v_6957 0 32);
      v_6968 <- eval (extract v_6938 32 64);
      v_6976 <- eval (extract v_6947 32 64);
      v_6985 <- eval (extract v_6957 32 64);
      v_6996 <- eval (extract v_6938 64 96);
      v_7004 <- eval (extract v_6947 64 96);
      v_7013 <- eval (extract v_6957 64 96);
      v_7023 <- eval (extract v_6938 96 128);
      v_7031 <- eval (extract v_6947 96 128);
      v_7040 <- eval (extract v_6957 96 128);
      v_7051 <- eval (extract v_6938 128 160);
      v_7059 <- eval (extract v_6947 128 160);
      v_7068 <- eval (extract v_6957 128 160);
      v_7078 <- eval (extract v_6938 160 192);
      v_7086 <- eval (extract v_6947 160 192);
      v_7095 <- eval (extract v_6957 160 192);
      v_7106 <- eval (extract v_6938 192 224);
      v_7114 <- eval (extract v_6947 192 224);
      v_7123 <- eval (extract v_6957 192 224);
      v_7133 <- eval (extract v_6938 224 256);
      v_7141 <- eval (extract v_6947 224 256);
      v_7150 <- eval (extract v_6957 224 256);
      setRegister (lhs.of_reg v_2752) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6939 0 1)) (uvalueMInt (extract v_6939 1 9)) (uvalueMInt (extract v_6939 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6948 0 1)) (uvalueMInt (extract v_6948 1 9)) (uvalueMInt (extract v_6948 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6958 0 1)) (uvalueMInt (extract v_6958 1 9)) (uvalueMInt (extract v_6958 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6968 0 1)) (uvalueMInt (extract v_6968 1 9)) (uvalueMInt (extract v_6968 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6976 0 1)) (uvalueMInt (extract v_6976 1 9)) (uvalueMInt (extract v_6976 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6985 0 1)) (uvalueMInt (extract v_6985 1 9)) (uvalueMInt (extract v_6985 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6996 0 1)) (uvalueMInt (extract v_6996 1 9)) (uvalueMInt (extract v_6996 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7004 0 1)) (uvalueMInt (extract v_7004 1 9)) (uvalueMInt (extract v_7004 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7013 0 1)) (uvalueMInt (extract v_7013 1 9)) (uvalueMInt (extract v_7013 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7023 0 1)) (uvalueMInt (extract v_7023 1 9)) (uvalueMInt (extract v_7023 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7031 0 1)) (uvalueMInt (extract v_7031 1 9)) (uvalueMInt (extract v_7031 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7040 0 1)) (uvalueMInt (extract v_7040 1 9)) (uvalueMInt (extract v_7040 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7051 0 1)) (uvalueMInt (extract v_7051 1 9)) (uvalueMInt (extract v_7051 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7059 0 1)) (uvalueMInt (extract v_7059 1 9)) (uvalueMInt (extract v_7059 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7068 0 1)) (uvalueMInt (extract v_7068 1 9)) (uvalueMInt (extract v_7068 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7078 0 1)) (uvalueMInt (extract v_7078 1 9)) (uvalueMInt (extract v_7078 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7086 0 1)) (uvalueMInt (extract v_7086 1 9)) (uvalueMInt (extract v_7086 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7095 0 1)) (uvalueMInt (extract v_7095 1 9)) (uvalueMInt (extract v_7095 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7106 0 1)) (uvalueMInt (extract v_7106 1 9)) (uvalueMInt (extract v_7106 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7114 0 1)) (uvalueMInt (extract v_7114 1 9)) (uvalueMInt (extract v_7114 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7123 0 1)) (uvalueMInt (extract v_7123 1 9)) (uvalueMInt (extract v_7123 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7133 0 1)) (uvalueMInt (extract v_7133 1 9)) (uvalueMInt (extract v_7133 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7141 0 1)) (uvalueMInt (extract v_7141 1 9)) (uvalueMInt (extract v_7141 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7150 0 1)) (uvalueMInt (extract v_7150 1 9)) (uvalueMInt (extract v_7150 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2736 : Mem) (v_2734 : reg (bv 128)) (v_2735 : reg (bv 128)) => do
      v_17649 <- getRegister v_2734;
      v_17650 <- eval (extract v_17649 0 32);
      v_17658 <- evaluateAddress v_2736;
      v_17659 <- load v_17658 16;
      v_17660 <- eval (extract v_17659 0 32);
      v_17669 <- getRegister v_2735;
      v_17670 <- eval (extract v_17669 0 32);
      v_17680 <- eval (extract v_17649 32 64);
      v_17688 <- eval (extract v_17659 32 64);
      v_17697 <- eval (extract v_17669 32 64);
      v_17708 <- eval (extract v_17649 64 96);
      v_17716 <- eval (extract v_17659 64 96);
      v_17725 <- eval (extract v_17669 64 96);
      v_17735 <- eval (extract v_17649 96 128);
      v_17743 <- eval (extract v_17659 96 128);
      v_17752 <- eval (extract v_17669 96 128);
      setRegister (lhs.of_reg v_2735) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17650 0 1)) (uvalueMInt (extract v_17650 1 9)) (uvalueMInt (extract v_17650 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17660 0 1)) (uvalueMInt (extract v_17660 1 9)) (uvalueMInt (extract v_17660 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17670 0 1)) (uvalueMInt (extract v_17670 1 9)) (uvalueMInt (extract v_17670 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17680 0 1)) (uvalueMInt (extract v_17680 1 9)) (uvalueMInt (extract v_17680 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17688 0 1)) (uvalueMInt (extract v_17688 1 9)) (uvalueMInt (extract v_17688 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17697 0 1)) (uvalueMInt (extract v_17697 1 9)) (uvalueMInt (extract v_17697 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17708 0 1)) (uvalueMInt (extract v_17708 1 9)) (uvalueMInt (extract v_17708 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17716 0 1)) (uvalueMInt (extract v_17716 1 9)) (uvalueMInt (extract v_17716 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17725 0 1)) (uvalueMInt (extract v_17725 1 9)) (uvalueMInt (extract v_17725 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17735 0 1)) (uvalueMInt (extract v_17735 1 9)) (uvalueMInt (extract v_17735 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17743 0 1)) (uvalueMInt (extract v_17743 1 9)) (uvalueMInt (extract v_17743 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17752 0 1)) (uvalueMInt (extract v_17752 1 9)) (uvalueMInt (extract v_17752 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2745 : Mem) (v_2746 : reg (bv 256)) (v_2747 : reg (bv 256)) => do
      v_17765 <- getRegister v_2746;
      v_17766 <- eval (extract v_17765 0 32);
      v_17774 <- evaluateAddress v_2745;
      v_17775 <- load v_17774 32;
      v_17776 <- eval (extract v_17775 0 32);
      v_17785 <- getRegister v_2747;
      v_17786 <- eval (extract v_17785 0 32);
      v_17796 <- eval (extract v_17765 32 64);
      v_17804 <- eval (extract v_17775 32 64);
      v_17813 <- eval (extract v_17785 32 64);
      v_17824 <- eval (extract v_17765 64 96);
      v_17832 <- eval (extract v_17775 64 96);
      v_17841 <- eval (extract v_17785 64 96);
      v_17851 <- eval (extract v_17765 96 128);
      v_17859 <- eval (extract v_17775 96 128);
      v_17868 <- eval (extract v_17785 96 128);
      v_17879 <- eval (extract v_17765 128 160);
      v_17887 <- eval (extract v_17775 128 160);
      v_17896 <- eval (extract v_17785 128 160);
      v_17906 <- eval (extract v_17765 160 192);
      v_17914 <- eval (extract v_17775 160 192);
      v_17923 <- eval (extract v_17785 160 192);
      v_17934 <- eval (extract v_17765 192 224);
      v_17942 <- eval (extract v_17775 192 224);
      v_17951 <- eval (extract v_17785 192 224);
      v_17961 <- eval (extract v_17765 224 256);
      v_17969 <- eval (extract v_17775 224 256);
      v_17978 <- eval (extract v_17785 224 256);
      setRegister (lhs.of_reg v_2747) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17766 0 1)) (uvalueMInt (extract v_17766 1 9)) (uvalueMInt (extract v_17766 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17776 0 1)) (uvalueMInt (extract v_17776 1 9)) (uvalueMInt (extract v_17776 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17786 0 1)) (uvalueMInt (extract v_17786 1 9)) (uvalueMInt (extract v_17786 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17796 0 1)) (uvalueMInt (extract v_17796 1 9)) (uvalueMInt (extract v_17796 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17804 0 1)) (uvalueMInt (extract v_17804 1 9)) (uvalueMInt (extract v_17804 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17813 0 1)) (uvalueMInt (extract v_17813 1 9)) (uvalueMInt (extract v_17813 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17824 0 1)) (uvalueMInt (extract v_17824 1 9)) (uvalueMInt (extract v_17824 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17832 0 1)) (uvalueMInt (extract v_17832 1 9)) (uvalueMInt (extract v_17832 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17841 0 1)) (uvalueMInt (extract v_17841 1 9)) (uvalueMInt (extract v_17841 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17851 0 1)) (uvalueMInt (extract v_17851 1 9)) (uvalueMInt (extract v_17851 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17859 0 1)) (uvalueMInt (extract v_17859 1 9)) (uvalueMInt (extract v_17859 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17868 0 1)) (uvalueMInt (extract v_17868 1 9)) (uvalueMInt (extract v_17868 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17879 0 1)) (uvalueMInt (extract v_17879 1 9)) (uvalueMInt (extract v_17879 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17887 0 1)) (uvalueMInt (extract v_17887 1 9)) (uvalueMInt (extract v_17887 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17896 0 1)) (uvalueMInt (extract v_17896 1 9)) (uvalueMInt (extract v_17896 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17906 0 1)) (uvalueMInt (extract v_17906 1 9)) (uvalueMInt (extract v_17906 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17914 0 1)) (uvalueMInt (extract v_17914 1 9)) (uvalueMInt (extract v_17914 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17923 0 1)) (uvalueMInt (extract v_17923 1 9)) (uvalueMInt (extract v_17923 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17934 0 1)) (uvalueMInt (extract v_17934 1 9)) (uvalueMInt (extract v_17934 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17942 0 1)) (uvalueMInt (extract v_17942 1 9)) (uvalueMInt (extract v_17942 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17951 0 1)) (uvalueMInt (extract v_17951 1 9)) (uvalueMInt (extract v_17951 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17961 0 1)) (uvalueMInt (extract v_17961 1 9)) (uvalueMInt (extract v_17961 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17969 0 1)) (uvalueMInt (extract v_17969 1 9)) (uvalueMInt (extract v_17969 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17978 0 1)) (uvalueMInt (extract v_17978 1 9)) (uvalueMInt (extract v_17978 9 32)))) 32)))));
      pure ()
    pat_end
