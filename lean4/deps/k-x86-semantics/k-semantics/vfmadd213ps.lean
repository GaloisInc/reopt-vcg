def vfmadd213ps1 : instruction :=
  definst "vfmadd213ps" $ do
    pattern fun (v_2519 : reg (bv 128)) (v_2520 : reg (bv 128)) (v_2521 : reg (bv 128)) => do
      v_4654 <- getRegister v_2520;
      v_4655 <- eval (extract v_4654 0 32);
      v_4663 <- getRegister v_2521;
      v_4664 <- eval (extract v_4663 0 32);
      v_4673 <- getRegister v_2519;
      v_4674 <- eval (extract v_4673 0 32);
      v_4681 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4674 0 1)) (uvalueMInt (extract v_4674 1 9)) (uvalueMInt (extract v_4674 9 32)));
      v_4689 <- eval (extract v_4654 32 64);
      v_4697 <- eval (extract v_4663 32 64);
      v_4706 <- eval (extract v_4673 32 64);
      v_4713 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4706 0 1)) (uvalueMInt (extract v_4706 1 9)) (uvalueMInt (extract v_4706 9 32)));
      v_4722 <- eval (extract v_4654 64 96);
      v_4730 <- eval (extract v_4663 64 96);
      v_4739 <- eval (extract v_4673 64 96);
      v_4746 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4739 0 1)) (uvalueMInt (extract v_4739 1 9)) (uvalueMInt (extract v_4739 9 32)));
      v_4754 <- eval (extract v_4654 96 128);
      v_4762 <- eval (extract v_4663 96 128);
      v_4771 <- eval (extract v_4673 96 128);
      v_4778 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4771 0 1)) (uvalueMInt (extract v_4771 1 9)) (uvalueMInt (extract v_4771 9 32)));
      setRegister (lhs.of_reg v_2521) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4655 0 1)) (uvalueMInt (extract v_4655 1 9)) (uvalueMInt (extract v_4655 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4664 0 1)) (uvalueMInt (extract v_4664 1 9)) (uvalueMInt (extract v_4664 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4681)) v_4681) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4689 0 1)) (uvalueMInt (extract v_4689 1 9)) (uvalueMInt (extract v_4689 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4697 0 1)) (uvalueMInt (extract v_4697 1 9)) (uvalueMInt (extract v_4697 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4713)) v_4713) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4722 0 1)) (uvalueMInt (extract v_4722 1 9)) (uvalueMInt (extract v_4722 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4730 0 1)) (uvalueMInt (extract v_4730 1 9)) (uvalueMInt (extract v_4730 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4746)) v_4746) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4754 0 1)) (uvalueMInt (extract v_4754 1 9)) (uvalueMInt (extract v_4754 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4762 0 1)) (uvalueMInt (extract v_4762 1 9)) (uvalueMInt (extract v_4762 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_4778)) v_4778) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2530 : reg (bv 256)) (v_2531 : reg (bv 256)) (v_2532 : reg (bv 256)) => do
      v_4794 <- getRegister v_2531;
      v_4795 <- eval (extract v_4794 0 32);
      v_4803 <- getRegister v_2532;
      v_4804 <- eval (extract v_4803 0 32);
      v_4813 <- getRegister v_2530;
      v_4814 <- eval (extract v_4813 0 32);
      v_4824 <- eval (extract v_4794 32 64);
      v_4832 <- eval (extract v_4803 32 64);
      v_4841 <- eval (extract v_4813 32 64);
      v_4852 <- eval (extract v_4794 64 96);
      v_4860 <- eval (extract v_4803 64 96);
      v_4869 <- eval (extract v_4813 64 96);
      v_4879 <- eval (extract v_4794 96 128);
      v_4887 <- eval (extract v_4803 96 128);
      v_4896 <- eval (extract v_4813 96 128);
      v_4906 <- eval (extract v_4794 128 160);
      v_4914 <- eval (extract v_4803 128 160);
      v_4923 <- eval (extract v_4813 128 160);
      v_4933 <- eval (extract v_4794 160 192);
      v_4941 <- eval (extract v_4803 160 192);
      v_4950 <- eval (extract v_4813 160 192);
      v_4960 <- eval (extract v_4794 192 224);
      v_4968 <- eval (extract v_4803 192 224);
      v_4977 <- eval (extract v_4813 192 224);
      v_4987 <- eval (extract v_4794 224 256);
      v_4995 <- eval (extract v_4803 224 256);
      v_5004 <- eval (extract v_4813 224 256);
      setRegister (lhs.of_reg v_2532) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4795 0 1)) (uvalueMInt (extract v_4795 1 9)) (uvalueMInt (extract v_4795 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4804 0 1)) (uvalueMInt (extract v_4804 1 9)) (uvalueMInt (extract v_4804 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4814 0 1)) (uvalueMInt (extract v_4814 1 9)) (uvalueMInt (extract v_4814 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4824 0 1)) (uvalueMInt (extract v_4824 1 9)) (uvalueMInt (extract v_4824 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4832 0 1)) (uvalueMInt (extract v_4832 1 9)) (uvalueMInt (extract v_4832 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4841 0 1)) (uvalueMInt (extract v_4841 1 9)) (uvalueMInt (extract v_4841 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4852 0 1)) (uvalueMInt (extract v_4852 1 9)) (uvalueMInt (extract v_4852 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4860 0 1)) (uvalueMInt (extract v_4860 1 9)) (uvalueMInt (extract v_4860 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4869 0 1)) (uvalueMInt (extract v_4869 1 9)) (uvalueMInt (extract v_4869 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4879 0 1)) (uvalueMInt (extract v_4879 1 9)) (uvalueMInt (extract v_4879 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4887 0 1)) (uvalueMInt (extract v_4887 1 9)) (uvalueMInt (extract v_4887 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4896 0 1)) (uvalueMInt (extract v_4896 1 9)) (uvalueMInt (extract v_4896 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4906 0 1)) (uvalueMInt (extract v_4906 1 9)) (uvalueMInt (extract v_4906 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4914 0 1)) (uvalueMInt (extract v_4914 1 9)) (uvalueMInt (extract v_4914 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4923 0 1)) (uvalueMInt (extract v_4923 1 9)) (uvalueMInt (extract v_4923 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4933 0 1)) (uvalueMInt (extract v_4933 1 9)) (uvalueMInt (extract v_4933 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4941 0 1)) (uvalueMInt (extract v_4941 1 9)) (uvalueMInt (extract v_4941 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4950 0 1)) (uvalueMInt (extract v_4950 1 9)) (uvalueMInt (extract v_4950 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4960 0 1)) (uvalueMInt (extract v_4960 1 9)) (uvalueMInt (extract v_4960 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4968 0 1)) (uvalueMInt (extract v_4968 1 9)) (uvalueMInt (extract v_4968 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4977 0 1)) (uvalueMInt (extract v_4977 1 9)) (uvalueMInt (extract v_4977 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4987 0 1)) (uvalueMInt (extract v_4987 1 9)) (uvalueMInt (extract v_4987 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4995 0 1)) (uvalueMInt (extract v_4995 1 9)) (uvalueMInt (extract v_4995 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5004 0 1)) (uvalueMInt (extract v_5004 1 9)) (uvalueMInt (extract v_5004 9 32)))) 32)))))));
      pure ()
    pat_end;
    pattern fun (v_2516 : Mem) (v_2514 : reg (bv 128)) (v_2515 : reg (bv 128)) => do
      v_15569 <- getRegister v_2514;
      v_15570 <- eval (extract v_15569 0 32);
      v_15578 <- getRegister v_2515;
      v_15579 <- eval (extract v_15578 0 32);
      v_15588 <- evaluateAddress v_2516;
      v_15589 <- load v_15588 16;
      v_15590 <- eval (extract v_15589 0 32);
      v_15597 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15590 0 1)) (uvalueMInt (extract v_15590 1 9)) (uvalueMInt (extract v_15590 9 32)));
      v_15605 <- eval (extract v_15569 32 64);
      v_15613 <- eval (extract v_15578 32 64);
      v_15622 <- eval (extract v_15589 32 64);
      v_15629 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15622 0 1)) (uvalueMInt (extract v_15622 1 9)) (uvalueMInt (extract v_15622 9 32)));
      v_15638 <- eval (extract v_15569 64 96);
      v_15646 <- eval (extract v_15578 64 96);
      v_15655 <- eval (extract v_15589 64 96);
      v_15662 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15655 0 1)) (uvalueMInt (extract v_15655 1 9)) (uvalueMInt (extract v_15655 9 32)));
      v_15670 <- eval (extract v_15569 96 128);
      v_15678 <- eval (extract v_15578 96 128);
      v_15687 <- eval (extract v_15589 96 128);
      v_15694 <- eval (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15687 0 1)) (uvalueMInt (extract v_15687 1 9)) (uvalueMInt (extract v_15687 9 32)));
      setRegister (lhs.of_reg v_2515) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15570 0 1)) (uvalueMInt (extract v_15570 1 9)) (uvalueMInt (extract v_15570 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15579 0 1)) (uvalueMInt (extract v_15579 1 9)) (uvalueMInt (extract v_15579 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_15597)) v_15597) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15605 0 1)) (uvalueMInt (extract v_15605 1 9)) (uvalueMInt (extract v_15605 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15613 0 1)) (uvalueMInt (extract v_15613 1 9)) (uvalueMInt (extract v_15613 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_15629)) v_15629) 32) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15638 0 1)) (uvalueMInt (extract v_15638 1 9)) (uvalueMInt (extract v_15638 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15646 0 1)) (uvalueMInt (extract v_15646 1 9)) (uvalueMInt (extract v_15646 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_15662)) v_15662) 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15670 0 1)) (uvalueMInt (extract v_15670 1 9)) (uvalueMInt (extract v_15670 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15678 0 1)) (uvalueMInt (extract v_15678 1 9)) (uvalueMInt (extract v_15678 9 32)))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_15694)) v_15694) 32) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2525 : Mem) (v_2526 : reg (bv 256)) (v_2527 : reg (bv 256)) => do
      v_15705 <- getRegister v_2526;
      v_15706 <- eval (extract v_15705 0 32);
      v_15714 <- getRegister v_2527;
      v_15715 <- eval (extract v_15714 0 32);
      v_15724 <- evaluateAddress v_2525;
      v_15725 <- load v_15724 32;
      v_15726 <- eval (extract v_15725 0 32);
      v_15736 <- eval (extract v_15705 32 64);
      v_15744 <- eval (extract v_15714 32 64);
      v_15753 <- eval (extract v_15725 32 64);
      v_15764 <- eval (extract v_15705 64 96);
      v_15772 <- eval (extract v_15714 64 96);
      v_15781 <- eval (extract v_15725 64 96);
      v_15791 <- eval (extract v_15705 96 128);
      v_15799 <- eval (extract v_15714 96 128);
      v_15808 <- eval (extract v_15725 96 128);
      v_15818 <- eval (extract v_15705 128 160);
      v_15826 <- eval (extract v_15714 128 160);
      v_15835 <- eval (extract v_15725 128 160);
      v_15845 <- eval (extract v_15705 160 192);
      v_15853 <- eval (extract v_15714 160 192);
      v_15862 <- eval (extract v_15725 160 192);
      v_15872 <- eval (extract v_15705 192 224);
      v_15880 <- eval (extract v_15714 192 224);
      v_15889 <- eval (extract v_15725 192 224);
      v_15899 <- eval (extract v_15705 224 256);
      v_15907 <- eval (extract v_15714 224 256);
      v_15916 <- eval (extract v_15725 224 256);
      setRegister (lhs.of_reg v_2527) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15706 0 1)) (uvalueMInt (extract v_15706 1 9)) (uvalueMInt (extract v_15706 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15715 0 1)) (uvalueMInt (extract v_15715 1 9)) (uvalueMInt (extract v_15715 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15726 0 1)) (uvalueMInt (extract v_15726 1 9)) (uvalueMInt (extract v_15726 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15736 0 1)) (uvalueMInt (extract v_15736 1 9)) (uvalueMInt (extract v_15736 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15744 0 1)) (uvalueMInt (extract v_15744 1 9)) (uvalueMInt (extract v_15744 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15753 0 1)) (uvalueMInt (extract v_15753 1 9)) (uvalueMInt (extract v_15753 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15764 0 1)) (uvalueMInt (extract v_15764 1 9)) (uvalueMInt (extract v_15764 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15772 0 1)) (uvalueMInt (extract v_15772 1 9)) (uvalueMInt (extract v_15772 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15781 0 1)) (uvalueMInt (extract v_15781 1 9)) (uvalueMInt (extract v_15781 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15791 0 1)) (uvalueMInt (extract v_15791 1 9)) (uvalueMInt (extract v_15791 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15799 0 1)) (uvalueMInt (extract v_15799 1 9)) (uvalueMInt (extract v_15799 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15808 0 1)) (uvalueMInt (extract v_15808 1 9)) (uvalueMInt (extract v_15808 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15818 0 1)) (uvalueMInt (extract v_15818 1 9)) (uvalueMInt (extract v_15818 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15826 0 1)) (uvalueMInt (extract v_15826 1 9)) (uvalueMInt (extract v_15826 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15835 0 1)) (uvalueMInt (extract v_15835 1 9)) (uvalueMInt (extract v_15835 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15845 0 1)) (uvalueMInt (extract v_15845 1 9)) (uvalueMInt (extract v_15845 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15853 0 1)) (uvalueMInt (extract v_15853 1 9)) (uvalueMInt (extract v_15853 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15862 0 1)) (uvalueMInt (extract v_15862 1 9)) (uvalueMInt (extract v_15862 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15872 0 1)) (uvalueMInt (extract v_15872 1 9)) (uvalueMInt (extract v_15872 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15880 0 1)) (uvalueMInt (extract v_15880 1 9)) (uvalueMInt (extract v_15880 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15889 0 1)) (uvalueMInt (extract v_15889 1 9)) (uvalueMInt (extract v_15889 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15899 0 1)) (uvalueMInt (extract v_15899 1 9)) (uvalueMInt (extract v_15899 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15907 0 1)) (uvalueMInt (extract v_15907 1 9)) (uvalueMInt (extract v_15907 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15916 0 1)) (uvalueMInt (extract v_15916 1 9)) (uvalueMInt (extract v_15916 9 32)))) 32)))))));
      pure ()
    pat_end
