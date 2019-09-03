def pmaxsd1 : instruction :=
  definst "pmaxsd" $ do
    pattern fun (v_2571 : reg (bv 128)) (v_2572 : reg (bv 128)) => do
      v_4787 <- getRegister v_2572;
      v_4788 <- eval (extract v_4787 0 32);
      v_4789 <- getRegister v_2571;
      v_4790 <- eval (extract v_4789 0 32);
      v_4793 <- eval (extract v_4787 32 64);
      v_4794 <- eval (extract v_4789 32 64);
      v_4797 <- eval (extract v_4787 64 96);
      v_4798 <- eval (extract v_4789 64 96);
      v_4801 <- eval (extract v_4787 96 128);
      v_4802 <- eval (extract v_4789 96 128);
      setRegister (lhs.of_reg v_2572) (concat (mux (sgt v_4788 v_4790) v_4788 v_4790) (concat (mux (sgt v_4793 v_4794) v_4793 v_4794) (concat (mux (sgt v_4797 v_4798) v_4797 v_4798) (mux (sgt v_4801 v_4802) v_4801 v_4802))));
      pure ()
    pat_end;
    pattern fun (v_2567 : Mem) (v_2568 : reg (bv 128)) => do
      v_11861 <- getRegister v_2568;
      v_11862 <- eval (extract v_11861 0 32);
      v_11863 <- evaluateAddress v_2567;
      v_11864 <- load v_11863 16;
      v_11865 <- eval (extract v_11864 0 32);
      v_11868 <- eval (extract v_11861 32 64);
      v_11869 <- eval (extract v_11864 32 64);
      v_11872 <- eval (extract v_11861 64 96);
      v_11873 <- eval (extract v_11864 64 96);
      v_11876 <- eval (extract v_11861 96 128);
      v_11877 <- eval (extract v_11864 96 128);
      setRegister (lhs.of_reg v_2568) (concat (mux (sgt v_11862 v_11865) v_11862 v_11865) (concat (mux (sgt v_11868 v_11869) v_11868 v_11869) (concat (mux (sgt v_11872 v_11873) v_11872 v_11873) (mux (sgt v_11876 v_11877) v_11876 v_11877))));
      pure ()
    pat_end
