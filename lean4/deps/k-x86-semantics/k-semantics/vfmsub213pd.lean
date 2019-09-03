def vfmsub213pd1 : instruction :=
  definst "vfmsub213pd" $ do
    pattern fun (v_2827 : reg (bv 128)) (v_2828 : reg (bv 128)) (v_2829 : reg (bv 128)) => do
      v_7782 <- getRegister v_2828;
      v_7783 <- eval (extract v_7782 0 64);
      v_7791 <- getRegister v_2829;
      v_7792 <- eval (extract v_7791 0 64);
      v_7801 <- getRegister v_2827;
      v_7802 <- eval (extract v_7801 0 64);
      v_7811 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7783 0 1)) (uvalueMInt (extract v_7783 1 12)) (uvalueMInt (extract v_7783 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7792 0 1)) (uvalueMInt (extract v_7792 1 12)) (uvalueMInt (extract v_7792 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7802 0 1)) (uvalueMInt (extract v_7802 1 12)) (uvalueMInt (extract v_7802 12 64)))) 64);
      v_7815 <- eval (extract v_7782 64 128);
      v_7823 <- eval (extract v_7791 64 128);
      v_7832 <- eval (extract v_7801 64 128);
      setRegister (lhs.of_reg v_2829) (concat (concat (extract v_7811 0 56) (extract v_7811 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7815 0 1)) (uvalueMInt (extract v_7815 1 12)) (uvalueMInt (extract v_7815 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7823 0 1)) (uvalueMInt (extract v_7823 1 12)) (uvalueMInt (extract v_7823 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7832 0 1)) (uvalueMInt (extract v_7832 1 12)) (uvalueMInt (extract v_7832 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2838 : reg (bv 256)) (v_2839 : reg (bv 256)) (v_2840 : reg (bv 256)) => do
      v_7849 <- getRegister v_2839;
      v_7850 <- eval (extract v_7849 0 64);
      v_7858 <- getRegister v_2840;
      v_7859 <- eval (extract v_7858 0 64);
      v_7868 <- getRegister v_2838;
      v_7869 <- eval (extract v_7868 0 64);
      v_7879 <- eval (extract v_7849 64 128);
      v_7887 <- eval (extract v_7858 64 128);
      v_7896 <- eval (extract v_7868 64 128);
      v_7906 <- eval (extract v_7849 128 192);
      v_7914 <- eval (extract v_7858 128 192);
      v_7923 <- eval (extract v_7868 128 192);
      v_7933 <- eval (extract v_7849 192 256);
      v_7941 <- eval (extract v_7858 192 256);
      v_7950 <- eval (extract v_7868 192 256);
      setRegister (lhs.of_reg v_2840) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7850 0 1)) (uvalueMInt (extract v_7850 1 12)) (uvalueMInt (extract v_7850 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7859 0 1)) (uvalueMInt (extract v_7859 1 12)) (uvalueMInt (extract v_7859 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7869 0 1)) (uvalueMInt (extract v_7869 1 12)) (uvalueMInt (extract v_7869 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7879 0 1)) (uvalueMInt (extract v_7879 1 12)) (uvalueMInt (extract v_7879 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7887 0 1)) (uvalueMInt (extract v_7887 1 12)) (uvalueMInt (extract v_7887 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7896 0 1)) (uvalueMInt (extract v_7896 1 12)) (uvalueMInt (extract v_7896 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7906 0 1)) (uvalueMInt (extract v_7906 1 12)) (uvalueMInt (extract v_7906 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7914 0 1)) (uvalueMInt (extract v_7914 1 12)) (uvalueMInt (extract v_7914 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7923 0 1)) (uvalueMInt (extract v_7923 1 12)) (uvalueMInt (extract v_7923 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7933 0 1)) (uvalueMInt (extract v_7933 1 12)) (uvalueMInt (extract v_7933 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7941 0 1)) (uvalueMInt (extract v_7941 1 12)) (uvalueMInt (extract v_7941 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7950 0 1)) (uvalueMInt (extract v_7950 1 12)) (uvalueMInt (extract v_7950 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_2824 : Mem) (v_2822 : reg (bv 128)) (v_2823 : reg (bv 128)) => do
      v_18579 <- getRegister v_2822;
      v_18580 <- eval (extract v_18579 0 64);
      v_18588 <- getRegister v_2823;
      v_18589 <- eval (extract v_18588 0 64);
      v_18598 <- evaluateAddress v_2824;
      v_18599 <- load v_18598 16;
      v_18600 <- eval (extract v_18599 0 64);
      v_18609 <- eval (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18580 0 1)) (uvalueMInt (extract v_18580 1 12)) (uvalueMInt (extract v_18580 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18589 0 1)) (uvalueMInt (extract v_18589 1 12)) (uvalueMInt (extract v_18589 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18600 0 1)) (uvalueMInt (extract v_18600 1 12)) (uvalueMInt (extract v_18600 12 64)))) 64);
      v_18613 <- eval (extract v_18579 64 128);
      v_18621 <- eval (extract v_18588 64 128);
      v_18630 <- eval (extract v_18599 64 128);
      setRegister (lhs.of_reg v_2823) (concat (concat (extract v_18609 0 56) (extract v_18609 56 64)) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18613 0 1)) (uvalueMInt (extract v_18613 1 12)) (uvalueMInt (extract v_18613 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18621 0 1)) (uvalueMInt (extract v_18621 1 12)) (uvalueMInt (extract v_18621 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18630 0 1)) (uvalueMInt (extract v_18630 1 12)) (uvalueMInt (extract v_18630 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2833 : Mem) (v_2834 : reg (bv 256)) (v_2835 : reg (bv 256)) => do
      v_18642 <- getRegister v_2834;
      v_18643 <- eval (extract v_18642 0 64);
      v_18651 <- getRegister v_2835;
      v_18652 <- eval (extract v_18651 0 64);
      v_18661 <- evaluateAddress v_2833;
      v_18662 <- load v_18661 32;
      v_18663 <- eval (extract v_18662 0 64);
      v_18673 <- eval (extract v_18642 64 128);
      v_18681 <- eval (extract v_18651 64 128);
      v_18690 <- eval (extract v_18662 64 128);
      v_18700 <- eval (extract v_18642 128 192);
      v_18708 <- eval (extract v_18651 128 192);
      v_18717 <- eval (extract v_18662 128 192);
      v_18727 <- eval (extract v_18642 192 256);
      v_18735 <- eval (extract v_18651 192 256);
      v_18744 <- eval (extract v_18662 192 256);
      setRegister (lhs.of_reg v_2835) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18643 0 1)) (uvalueMInt (extract v_18643 1 12)) (uvalueMInt (extract v_18643 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18652 0 1)) (uvalueMInt (extract v_18652 1 12)) (uvalueMInt (extract v_18652 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18663 0 1)) (uvalueMInt (extract v_18663 1 12)) (uvalueMInt (extract v_18663 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18673 0 1)) (uvalueMInt (extract v_18673 1 12)) (uvalueMInt (extract v_18673 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18681 0 1)) (uvalueMInt (extract v_18681 1 12)) (uvalueMInt (extract v_18681 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18690 0 1)) (uvalueMInt (extract v_18690 1 12)) (uvalueMInt (extract v_18690 12 64)))) 64) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18700 0 1)) (uvalueMInt (extract v_18700 1 12)) (uvalueMInt (extract v_18700 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18708 0 1)) (uvalueMInt (extract v_18708 1 12)) (uvalueMInt (extract v_18708 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18717 0 1)) (uvalueMInt (extract v_18717 1 12)) (uvalueMInt (extract v_18717 12 64)))) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18727 0 1)) (uvalueMInt (extract v_18727 1 12)) (uvalueMInt (extract v_18727 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18735 0 1)) (uvalueMInt (extract v_18735 1 12)) (uvalueMInt (extract v_18735 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_18744 0 1)) (uvalueMInt (extract v_18744 1 12)) (uvalueMInt (extract v_18744 12 64)))) 64))));
      pure ()
    pat_end
