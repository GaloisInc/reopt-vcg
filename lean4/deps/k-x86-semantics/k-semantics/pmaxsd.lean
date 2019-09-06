def pmaxsd1 : instruction :=
  definst "pmaxsd" $ do
    pattern fun (v_2648 : reg (bv 128)) (v_2649 : reg (bv 128)) => do
      v_4845 <- getRegister v_2649;
      v_4846 <- eval (extract v_4845 0 32);
      v_4847 <- getRegister v_2648;
      v_4848 <- eval (extract v_4847 0 32);
      v_4851 <- eval (extract v_4845 32 64);
      v_4852 <- eval (extract v_4847 32 64);
      v_4855 <- eval (extract v_4845 64 96);
      v_4856 <- eval (extract v_4847 64 96);
      v_4859 <- eval (extract v_4845 96 128);
      v_4860 <- eval (extract v_4847 96 128);
      setRegister (lhs.of_reg v_2649) (concat (mux (sgt v_4846 v_4848) v_4846 v_4848) (concat (mux (sgt v_4851 v_4852) v_4851 v_4852) (concat (mux (sgt v_4855 v_4856) v_4855 v_4856) (mux (sgt v_4859 v_4860) v_4859 v_4860))));
      pure ()
    pat_end;
    pattern fun (v_2644 : Mem) (v_2645 : reg (bv 128)) => do
      v_11695 <- getRegister v_2645;
      v_11696 <- eval (extract v_11695 0 32);
      v_11697 <- evaluateAddress v_2644;
      v_11698 <- load v_11697 16;
      v_11699 <- eval (extract v_11698 0 32);
      v_11702 <- eval (extract v_11695 32 64);
      v_11703 <- eval (extract v_11698 32 64);
      v_11706 <- eval (extract v_11695 64 96);
      v_11707 <- eval (extract v_11698 64 96);
      v_11710 <- eval (extract v_11695 96 128);
      v_11711 <- eval (extract v_11698 96 128);
      setRegister (lhs.of_reg v_2645) (concat (mux (sgt v_11696 v_11699) v_11696 v_11699) (concat (mux (sgt v_11702 v_11703) v_11702 v_11703) (concat (mux (sgt v_11706 v_11707) v_11706 v_11707) (mux (sgt v_11710 v_11711) v_11710 v_11711))));
      pure ()
    pat_end
