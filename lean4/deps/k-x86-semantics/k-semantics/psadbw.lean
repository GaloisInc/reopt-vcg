def psadbw1 : instruction :=
  definst "psadbw" $ do
    pattern fun (v_2881 : reg (bv 128)) (v_2882 : reg (bv 128)) => do
      v_6572 <- getRegister v_2882;
      v_6573 <- eval (extract v_6572 0 8);
      v_6574 <- getRegister v_2881;
      v_6575 <- eval (extract v_6574 0 8);
      v_6581 <- eval (extract v_6572 8 16);
      v_6582 <- eval (extract v_6574 8 16);
      v_6588 <- eval (extract v_6572 16 24);
      v_6589 <- eval (extract v_6574 16 24);
      v_6595 <- eval (extract v_6572 24 32);
      v_6596 <- eval (extract v_6574 24 32);
      v_6602 <- eval (extract v_6572 32 40);
      v_6603 <- eval (extract v_6574 32 40);
      v_6609 <- eval (extract v_6572 40 48);
      v_6610 <- eval (extract v_6574 40 48);
      v_6616 <- eval (extract v_6572 48 56);
      v_6617 <- eval (extract v_6574 48 56);
      v_6623 <- eval (extract v_6572 56 64);
      v_6624 <- eval (extract v_6574 56 64);
      v_6637 <- eval (extract v_6572 64 72);
      v_6638 <- eval (extract v_6574 64 72);
      v_6644 <- eval (extract v_6572 72 80);
      v_6645 <- eval (extract v_6574 72 80);
      v_6651 <- eval (extract v_6572 80 88);
      v_6652 <- eval (extract v_6574 80 88);
      v_6658 <- eval (extract v_6572 88 96);
      v_6659 <- eval (extract v_6574 88 96);
      v_6665 <- eval (extract v_6572 96 104);
      v_6666 <- eval (extract v_6574 96 104);
      v_6672 <- eval (extract v_6572 104 112);
      v_6673 <- eval (extract v_6574 104 112);
      v_6679 <- eval (extract v_6572 112 120);
      v_6680 <- eval (extract v_6574 112 120);
      v_6686 <- eval (extract v_6572 120 128);
      v_6687 <- eval (extract v_6574 120 128);
      setRegister (lhs.of_reg v_2882) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_6573 v_6575) (sub v_6573 v_6575) (sub v_6575 v_6573))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6581 v_6582) (sub v_6581 v_6582) (sub v_6582 v_6581))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6588 v_6589) (sub v_6588 v_6589) (sub v_6589 v_6588))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6595 v_6596) (sub v_6595 v_6596) (sub v_6596 v_6595))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6602 v_6603) (sub v_6602 v_6603) (sub v_6603 v_6602))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6609 v_6610) (sub v_6609 v_6610) (sub v_6610 v_6609))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6616 v_6617) (sub v_6616 v_6617) (sub v_6617 v_6616))) (concat (expression.bv_nat 8 0) (mux (ugt v_6623 v_6624) (sub v_6623 v_6624) (sub v_6624 v_6623)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6637 v_6638) (sub v_6637 v_6638) (sub v_6638 v_6637))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6644 v_6645) (sub v_6644 v_6645) (sub v_6645 v_6644))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6651 v_6652) (sub v_6651 v_6652) (sub v_6652 v_6651))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6658 v_6659) (sub v_6658 v_6659) (sub v_6659 v_6658))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6665 v_6666) (sub v_6665 v_6666) (sub v_6666 v_6665))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6672 v_6673) (sub v_6672 v_6673) (sub v_6673 v_6672))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6679 v_6680) (sub v_6679 v_6680) (sub v_6680 v_6679))) (concat (expression.bv_nat 8 0) (mux (ugt v_6686 v_6687) (sub v_6686 v_6687) (sub v_6687 v_6686)))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2876 : Mem) (v_2877 : reg (bv 128)) => do
      v_13802 <- getRegister v_2877;
      v_13803 <- eval (extract v_13802 0 8);
      v_13804 <- evaluateAddress v_2876;
      v_13805 <- load v_13804 16;
      v_13806 <- eval (extract v_13805 0 8);
      v_13812 <- eval (extract v_13802 8 16);
      v_13813 <- eval (extract v_13805 8 16);
      v_13819 <- eval (extract v_13802 16 24);
      v_13820 <- eval (extract v_13805 16 24);
      v_13826 <- eval (extract v_13802 24 32);
      v_13827 <- eval (extract v_13805 24 32);
      v_13833 <- eval (extract v_13802 32 40);
      v_13834 <- eval (extract v_13805 32 40);
      v_13840 <- eval (extract v_13802 40 48);
      v_13841 <- eval (extract v_13805 40 48);
      v_13847 <- eval (extract v_13802 48 56);
      v_13848 <- eval (extract v_13805 48 56);
      v_13854 <- eval (extract v_13802 56 64);
      v_13855 <- eval (extract v_13805 56 64);
      v_13868 <- eval (extract v_13802 64 72);
      v_13869 <- eval (extract v_13805 64 72);
      v_13875 <- eval (extract v_13802 72 80);
      v_13876 <- eval (extract v_13805 72 80);
      v_13882 <- eval (extract v_13802 80 88);
      v_13883 <- eval (extract v_13805 80 88);
      v_13889 <- eval (extract v_13802 88 96);
      v_13890 <- eval (extract v_13805 88 96);
      v_13896 <- eval (extract v_13802 96 104);
      v_13897 <- eval (extract v_13805 96 104);
      v_13903 <- eval (extract v_13802 104 112);
      v_13904 <- eval (extract v_13805 104 112);
      v_13910 <- eval (extract v_13802 112 120);
      v_13911 <- eval (extract v_13805 112 120);
      v_13917 <- eval (extract v_13802 120 128);
      v_13918 <- eval (extract v_13805 120 128);
      setRegister (lhs.of_reg v_2877) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_13803 v_13806) (sub v_13803 v_13806) (sub v_13806 v_13803))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13812 v_13813) (sub v_13812 v_13813) (sub v_13813 v_13812))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13819 v_13820) (sub v_13819 v_13820) (sub v_13820 v_13819))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13826 v_13827) (sub v_13826 v_13827) (sub v_13827 v_13826))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13833 v_13834) (sub v_13833 v_13834) (sub v_13834 v_13833))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13840 v_13841) (sub v_13840 v_13841) (sub v_13841 v_13840))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13847 v_13848) (sub v_13847 v_13848) (sub v_13848 v_13847))) (concat (expression.bv_nat 8 0) (mux (ugt v_13854 v_13855) (sub v_13854 v_13855) (sub v_13855 v_13854)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13868 v_13869) (sub v_13868 v_13869) (sub v_13869 v_13868))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13875 v_13876) (sub v_13875 v_13876) (sub v_13876 v_13875))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13882 v_13883) (sub v_13882 v_13883) (sub v_13883 v_13882))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13889 v_13890) (sub v_13889 v_13890) (sub v_13890 v_13889))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13896 v_13897) (sub v_13896 v_13897) (sub v_13897 v_13896))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13903 v_13904) (sub v_13903 v_13904) (sub v_13904 v_13903))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13910 v_13911) (sub v_13910 v_13911) (sub v_13911 v_13910))) (concat (expression.bv_nat 8 0) (mux (ugt v_13917 v_13918) (sub v_13917 v_13918) (sub v_13918 v_13917)))))))))))));
      pure ()
    pat_end
