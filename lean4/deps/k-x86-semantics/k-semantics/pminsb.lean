def pminsb1 : instruction :=
  definst "pminsb" $ do
    pattern fun (v_2665 : reg (bv 128)) (v_2666 : reg (bv 128)) => do
      v_5048 <- getRegister v_2666;
      v_5049 <- eval (extract v_5048 0 8);
      v_5050 <- getRegister v_2665;
      v_5051 <- eval (extract v_5050 0 8);
      v_5054 <- eval (extract v_5048 8 16);
      v_5055 <- eval (extract v_5050 8 16);
      v_5058 <- eval (extract v_5048 16 24);
      v_5059 <- eval (extract v_5050 16 24);
      v_5062 <- eval (extract v_5048 24 32);
      v_5063 <- eval (extract v_5050 24 32);
      v_5066 <- eval (extract v_5048 32 40);
      v_5067 <- eval (extract v_5050 32 40);
      v_5070 <- eval (extract v_5048 40 48);
      v_5071 <- eval (extract v_5050 40 48);
      v_5074 <- eval (extract v_5048 48 56);
      v_5075 <- eval (extract v_5050 48 56);
      v_5078 <- eval (extract v_5048 56 64);
      v_5079 <- eval (extract v_5050 56 64);
      v_5082 <- eval (extract v_5048 64 72);
      v_5083 <- eval (extract v_5050 64 72);
      v_5086 <- eval (extract v_5048 72 80);
      v_5087 <- eval (extract v_5050 72 80);
      v_5090 <- eval (extract v_5048 80 88);
      v_5091 <- eval (extract v_5050 80 88);
      v_5094 <- eval (extract v_5048 88 96);
      v_5095 <- eval (extract v_5050 88 96);
      v_5098 <- eval (extract v_5048 96 104);
      v_5099 <- eval (extract v_5050 96 104);
      v_5102 <- eval (extract v_5048 104 112);
      v_5103 <- eval (extract v_5050 104 112);
      v_5106 <- eval (extract v_5048 112 120);
      v_5107 <- eval (extract v_5050 112 120);
      v_5110 <- eval (extract v_5048 120 128);
      v_5111 <- eval (extract v_5050 120 128);
      setRegister (lhs.of_reg v_2666) (concat (mux (slt v_5049 v_5051) v_5049 v_5051) (concat (mux (slt v_5054 v_5055) v_5054 v_5055) (concat (mux (slt v_5058 v_5059) v_5058 v_5059) (concat (mux (slt v_5062 v_5063) v_5062 v_5063) (concat (mux (slt v_5066 v_5067) v_5066 v_5067) (concat (mux (slt v_5070 v_5071) v_5070 v_5071) (concat (mux (slt v_5074 v_5075) v_5074 v_5075) (concat (mux (slt v_5078 v_5079) v_5078 v_5079) (concat (mux (slt v_5082 v_5083) v_5082 v_5083) (concat (mux (slt v_5086 v_5087) v_5086 v_5087) (concat (mux (slt v_5090 v_5091) v_5090 v_5091) (concat (mux (slt v_5094 v_5095) v_5094 v_5095) (concat (mux (slt v_5098 v_5099) v_5098 v_5099) (concat (mux (slt v_5102 v_5103) v_5102 v_5103) (concat (mux (slt v_5106 v_5107) v_5106 v_5107) (mux (slt v_5110 v_5111) v_5110 v_5111))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2662 : Mem) (v_2661 : reg (bv 128)) => do
      v_11934 <- getRegister v_2661;
      v_11935 <- eval (extract v_11934 0 8);
      v_11936 <- evaluateAddress v_2662;
      v_11937 <- load v_11936 16;
      v_11938 <- eval (extract v_11937 0 8);
      v_11941 <- eval (extract v_11934 8 16);
      v_11942 <- eval (extract v_11937 8 16);
      v_11945 <- eval (extract v_11934 16 24);
      v_11946 <- eval (extract v_11937 16 24);
      v_11949 <- eval (extract v_11934 24 32);
      v_11950 <- eval (extract v_11937 24 32);
      v_11953 <- eval (extract v_11934 32 40);
      v_11954 <- eval (extract v_11937 32 40);
      v_11957 <- eval (extract v_11934 40 48);
      v_11958 <- eval (extract v_11937 40 48);
      v_11961 <- eval (extract v_11934 48 56);
      v_11962 <- eval (extract v_11937 48 56);
      v_11965 <- eval (extract v_11934 56 64);
      v_11966 <- eval (extract v_11937 56 64);
      v_11969 <- eval (extract v_11934 64 72);
      v_11970 <- eval (extract v_11937 64 72);
      v_11973 <- eval (extract v_11934 72 80);
      v_11974 <- eval (extract v_11937 72 80);
      v_11977 <- eval (extract v_11934 80 88);
      v_11978 <- eval (extract v_11937 80 88);
      v_11981 <- eval (extract v_11934 88 96);
      v_11982 <- eval (extract v_11937 88 96);
      v_11985 <- eval (extract v_11934 96 104);
      v_11986 <- eval (extract v_11937 96 104);
      v_11989 <- eval (extract v_11934 104 112);
      v_11990 <- eval (extract v_11937 104 112);
      v_11993 <- eval (extract v_11934 112 120);
      v_11994 <- eval (extract v_11937 112 120);
      v_11997 <- eval (extract v_11934 120 128);
      v_11998 <- eval (extract v_11937 120 128);
      setRegister (lhs.of_reg v_2661) (concat (mux (slt v_11935 v_11938) v_11935 v_11938) (concat (mux (slt v_11941 v_11942) v_11941 v_11942) (concat (mux (slt v_11945 v_11946) v_11945 v_11946) (concat (mux (slt v_11949 v_11950) v_11949 v_11950) (concat (mux (slt v_11953 v_11954) v_11953 v_11954) (concat (mux (slt v_11957 v_11958) v_11957 v_11958) (concat (mux (slt v_11961 v_11962) v_11961 v_11962) (concat (mux (slt v_11965 v_11966) v_11965 v_11966) (concat (mux (slt v_11969 v_11970) v_11969 v_11970) (concat (mux (slt v_11973 v_11974) v_11973 v_11974) (concat (mux (slt v_11977 v_11978) v_11977 v_11978) (concat (mux (slt v_11981 v_11982) v_11981 v_11982) (concat (mux (slt v_11985 v_11986) v_11985 v_11986) (concat (mux (slt v_11989 v_11990) v_11989 v_11990) (concat (mux (slt v_11993 v_11994) v_11993 v_11994) (mux (slt v_11997 v_11998) v_11997 v_11998))))))))))))))));
      pure ()
    pat_end
