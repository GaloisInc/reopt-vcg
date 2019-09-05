def pmaxud1 : instruction :=
  definst "pmaxud" $ do
    pattern fun (v_2647 : reg (bv 128)) (v_2648 : reg (bv 128)) => do
      v_4976 <- getRegister v_2648;
      v_4977 <- eval (extract v_4976 0 32);
      v_4978 <- getRegister v_2647;
      v_4979 <- eval (extract v_4978 0 32);
      v_4982 <- eval (extract v_4976 32 64);
      v_4983 <- eval (extract v_4978 32 64);
      v_4986 <- eval (extract v_4976 64 96);
      v_4987 <- eval (extract v_4978 64 96);
      v_4990 <- eval (extract v_4976 96 128);
      v_4991 <- eval (extract v_4978 96 128);
      setRegister (lhs.of_reg v_2648) (concat (mux (ugt v_4977 v_4979) v_4977 v_4979) (concat (mux (ugt v_4982 v_4983) v_4982 v_4983) (concat (mux (ugt v_4986 v_4987) v_4986 v_4987) (mux (ugt v_4990 v_4991) v_4990 v_4991))));
      pure ()
    pat_end;
    pattern fun (v_2644 : Mem) (v_2643 : reg (bv 128)) => do
      v_11868 <- getRegister v_2643;
      v_11869 <- eval (extract v_11868 0 32);
      v_11870 <- evaluateAddress v_2644;
      v_11871 <- load v_11870 16;
      v_11872 <- eval (extract v_11871 0 32);
      v_11875 <- eval (extract v_11868 32 64);
      v_11876 <- eval (extract v_11871 32 64);
      v_11879 <- eval (extract v_11868 64 96);
      v_11880 <- eval (extract v_11871 64 96);
      v_11883 <- eval (extract v_11868 96 128);
      v_11884 <- eval (extract v_11871 96 128);
      setRegister (lhs.of_reg v_2643) (concat (mux (ugt v_11869 v_11872) v_11869 v_11872) (concat (mux (ugt v_11875 v_11876) v_11875 v_11876) (concat (mux (ugt v_11879 v_11880) v_11879 v_11880) (mux (ugt v_11883 v_11884) v_11883 v_11884))));
      pure ()
    pat_end
