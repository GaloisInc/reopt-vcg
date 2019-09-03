def pmaxuw1 : instruction :=
  definst "pmaxuw" $ do
    pattern fun (v_2607 : reg (bv 128)) (v_2608 : reg (bv 128)) => do
      v_4971 <- getRegister v_2608;
      v_4972 <- eval (extract v_4971 0 16);
      v_4973 <- getRegister v_2607;
      v_4974 <- eval (extract v_4973 0 16);
      v_4977 <- eval (extract v_4971 16 32);
      v_4978 <- eval (extract v_4973 16 32);
      v_4981 <- eval (extract v_4971 32 48);
      v_4982 <- eval (extract v_4973 32 48);
      v_4985 <- eval (extract v_4971 48 64);
      v_4986 <- eval (extract v_4973 48 64);
      v_4989 <- eval (extract v_4971 64 80);
      v_4990 <- eval (extract v_4973 64 80);
      v_4993 <- eval (extract v_4971 80 96);
      v_4994 <- eval (extract v_4973 80 96);
      v_4997 <- eval (extract v_4971 96 112);
      v_4998 <- eval (extract v_4973 96 112);
      v_5001 <- eval (extract v_4971 112 128);
      v_5002 <- eval (extract v_4973 112 128);
      setRegister (lhs.of_reg v_2608) (concat (mux (ugt v_4972 v_4974) v_4972 v_4974) (concat (mux (ugt v_4977 v_4978) v_4977 v_4978) (concat (mux (ugt v_4981 v_4982) v_4981 v_4982) (concat (mux (ugt v_4985 v_4986) v_4985 v_4986) (concat (mux (ugt v_4989 v_4990) v_4989 v_4990) (concat (mux (ugt v_4993 v_4994) v_4993 v_4994) (concat (mux (ugt v_4997 v_4998) v_4997 v_4998) (mux (ugt v_5001 v_5002) v_5001 v_5002))))))));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) (v_2604 : reg (bv 128)) => do
      v_12033 <- getRegister v_2604;
      v_12034 <- eval (extract v_12033 0 16);
      v_12035 <- evaluateAddress v_2603;
      v_12036 <- load v_12035 16;
      v_12037 <- eval (extract v_12036 0 16);
      v_12040 <- eval (extract v_12033 16 32);
      v_12041 <- eval (extract v_12036 16 32);
      v_12044 <- eval (extract v_12033 32 48);
      v_12045 <- eval (extract v_12036 32 48);
      v_12048 <- eval (extract v_12033 48 64);
      v_12049 <- eval (extract v_12036 48 64);
      v_12052 <- eval (extract v_12033 64 80);
      v_12053 <- eval (extract v_12036 64 80);
      v_12056 <- eval (extract v_12033 80 96);
      v_12057 <- eval (extract v_12036 80 96);
      v_12060 <- eval (extract v_12033 96 112);
      v_12061 <- eval (extract v_12036 96 112);
      v_12064 <- eval (extract v_12033 112 128);
      v_12065 <- eval (extract v_12036 112 128);
      setRegister (lhs.of_reg v_2604) (concat (mux (ugt v_12034 v_12037) v_12034 v_12037) (concat (mux (ugt v_12040 v_12041) v_12040 v_12041) (concat (mux (ugt v_12044 v_12045) v_12044 v_12045) (concat (mux (ugt v_12048 v_12049) v_12048 v_12049) (concat (mux (ugt v_12052 v_12053) v_12052 v_12053) (concat (mux (ugt v_12056 v_12057) v_12056 v_12057) (concat (mux (ugt v_12060 v_12061) v_12060 v_12061) (mux (ugt v_12064 v_12065) v_12064 v_12065))))))));
      pure ()
    pat_end
