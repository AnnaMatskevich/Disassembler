import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

public class ElfParser {
    public ElfParser() {

    }

    public void parse(String inputFile, String outputFile) {
        Disassembler d = new Disassembler(inputFile, outputFile);
    }


    private static class Disassembler {
        int sectionHeadderOffset;
        int sectionNameIndexInSectionHeadder;
        int sectionHeadderSize = 40;
        int sectionNameOffset;
        int symtabOffset = 0;
        int symtabSize = 0;
        int strTabOffset = 0;
        int strtabSize = 0;
        int textOffset = 0;
        int textSize = 0;
        int textAddr = 0;
        int textLinesCount;
        int sectionHeadersCount;
        int symtabLineSize;
        private int[] bytes;
        private final Map<Integer, String> functionNames = new HashMap<>();
        private int lCount = 0;
        private static final Map<Integer, String> BIND = Map.of(
                0, "LOCAL",
                1, "GLOBAL",
                2, "WEAK",
                10, "LOOS",
                12, "HIOS",
                13, "LOPROC",
                15, "HIPROC"
        );

        private static final Map<Integer, String> TYPE = new HashMap<>();
        private static final Map<Integer, String> VISIBILITY = Map.of(
                0, "DEFAULT",
                1, "INTERNAL",
                2, "HIDDEN",
                3, "PROTECTED",
                4, "EXPORTED",
                5, "SINGLETON",
                6, "ELIMINATE"
        );

        private static final Map<Integer, String> INDEX = Map.of(
                0, "UNDEF",
                0xff00, "LOPROC",
                0xff1f, "HIPROC",
                0xff20, "LOOS",
                0xff3f, "HIOS",
                0xfff1, "ABS",
                0xfff2, "COMMON",
                0xffff, "XINDEX"
        );

        OutputStream outputStream;


        private Disassembler(String inputFile, String outputFile) {
            try {
                FileInputStream stream = new FileInputStream(inputFile);
                try {
                    bytes = new int[stream.available() + 1];
                    int k = stream.read();
                    int counter = 0;
                    while (k != -1) {
                        bytes[counter++] = k;
                        k = stream.read();
                    }

                } catch (IOException e) {
                    System.err.println("cant read from file");
                } finally {
                    stream.close();
                }
            } catch (IOException e) {
                System.err.println("file not found");
            }

            try {
                outputStream = new FileOutputStream(outputFile);
                try {
                    parseElf();
                } catch (IOException e) {
                    System.err.println("cant write to file");
                } finally {
                    outputStream.close();
                }
            } catch (IOException e) {
                System.err.println("no output file");
            }

        }

        private int bytesToInt(int first, int byteCount) {
            int ans = 0;
            for (int i = first + byteCount - 1; i >= first; i--) {
                ans = ans << 8;
                ans += bytes[i];
            }
            return ans;
        }

        private String bytestoString(int start) {
            StringBuilder sb = new StringBuilder();
            int k = 0;
            while (bytes[start + k] != 0) {
                sb.append((char) bytes[start + k]);
                k++;
            }
            return sb.toString();
        }

        private String rdConvert(int rd) {
            switch (rd) {
                case 0 -> {
                    return "zero";
                }
                case 1 -> {
                    return "ra";
                }
                case 2 -> {
                    return "sp";
                }
                case 3 -> {
                    return "gp";
                }
                case 4 -> {
                    return "tp";
                }
            }
            if (rd <= 7) {
                return "t" + (rd - 5);
            }
            if (rd <= 9) {
                return "s" + (rd - 8);
            }
            if (rd <= 17) {
                return "a" + (rd - 10);
            }
            if (rd <= 27) {
                return "s" + (rd - 16);
            }
            return "t" + (rd - 25);
        }

        private void AUIPC(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int imm = (code & 0b11111111111111111111000000000000) >> 12;
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s\n", addr, code, "auipc", rdConvert(rd), "0x" + Integer.toHexString(imm)).getBytes());
            }
        }

        private void LUI(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int imm = (code & 0b11111111111111111111000000000000) >> 12;
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s\n", addr, code, "lui", rdConvert(rd), "0x" + Integer.toHexString(imm)).getBytes());
            }
        }

        private void JAL(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int imm = ((code >> 21) & 0x3ff) +
                    (((code >> 20) & 1) << 10) +
                    (((code >> 12) & 0xff) << 11);
            imm = (((code >> 31) & 1) == 1 ? 0xfff00000 : 0) | (imm << 1);
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, 0x%x <%s>\n", addr, code, "jal", rdConvert(rd), imm + addr, functionNames.get(imm + addr)).getBytes(StandardCharsets.UTF_8));
            } else {
                if (!functionNames.containsKey(imm + addr)) {
                    functionNames.put(imm + addr, "L" + lCount);
                    lCount++;
                }
            }
        }

        private void JALR(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int rs1 = (code & 0b11111000000000000000) >> 15;
            int imm = (code & 0b11111111111100000000000000000000) >> 20;
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %d(%s)\n", addr, code, "jalr", rdConvert(rd), imm, rdConvert(rs1)).getBytes());
            }
        }

        private void B(int addr, int code, boolean needPrint) throws IOException {
            int rs1 = (code & 0b11111000000000000000) >> 15;
            int rs2 = (code & 0b1111100000000000000000000) >> 20;
            int func = (code & 0b111000000000000) >> 12;
            String name;
            switch (func) {
                case 0b000 -> name = "beq";
                case 0b001 -> name = "bne";
                case 0b100 -> name = "blt";
                case 0b101 -> name = "bge";
                case 0b110 -> name = "bltu";
                case 0b111 -> name = "bgeu";
                default -> {
                    invalidInstruction(addr, code, needPrint);
                    return;
                }
            }
            int imm = (((((code >> 25) & 0b111111) << 4) & 0x3ff) +
                    (((code >> 7) & 1) << 10) +
                    ((code >> 8) & 0b1111)) << 1;
            imm = (((code >> 31) & 1) == 1 ? 0xfffff000 : 0) | imm;

            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, 0x%x, <%s>\n", addr, code, name, rdConvert(rs1), rdConvert(rs2), imm + addr, functionNames.get(imm + addr)).getBytes()); // <...>
            } else {
                if (!functionNames.containsKey(imm + addr)) {
                    functionNames.put(imm + addr, "L" + lCount);
                    lCount++;
                }
            }
        }

        private void L(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int rs1 = (code & 0b11111000000000000000) >> 15;
            int imm = (code & 0b11111111111100000000000000000000) >> 20;
            int func = (code & 0b111000000000000) >> 12;
            String name;
            switch (func) {
                case 0b000 -> name = "lb";
                case 0b001 -> name = "lh";
                case 0b010 -> name = "lw";
                case 0b100 -> name = "lbu";
                case 0b101 -> name = "lhu";
                default -> {
                    invalidInstruction(addr, code, needPrint);
                    return;
                }

            }
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %d(%s)\n", addr, code, name, rdConvert(rd), imm, rdConvert(rs1)).getBytes());
            }
        }

        private void S(int addr, int code, boolean needPrint) throws IOException {
            int immLeft = (code & 0b11111110000000000000000000000000) >> 25;
            immLeft = immLeft << 5;
            int immRight = immLeft + ((code & 0b111110000000) >> 7);
            int rs1 = (code & 0b11111000000000000000) >> 15;
            int rs2 = (code & 0b1111100000000000000000000) >> 20;
            int func = (code & 0b111000000000000) >> 12;
            String name;
            switch (func) {
                case 0b000 -> name = "sb";
                case 0b001 -> name = "sh";
                case 0b010 -> name = "sw";
                default -> {
                    invalidInstruction(addr, code, needPrint);
                    return;
                }
            }
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %d(%s)\n", addr, code, name, rdConvert(rs2), immRight, rdConvert(rs1)).getBytes());
            }
        }

        private void ADDI_SRAI(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int rs1 = (code & 0b11111000000000000000) >> 15;
            int func = (code & 0b111000000000000) >> 12;
            int imm = (code & 0b11111111111100000000000000000000) >> 20;
            int shamt = (code & 0b1111100000000000000000000) >> 20;
            int funct7 = (code & 0b11111110000000000000000000000000) >> 25;
            if (needPrint) {
                switch (func) {
                    case 0b0 -> {
                        //ADDI
                        outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "addi", rdConvert(rd), rdConvert(rs1), imm).getBytes());
                        return;
                    }

                    case 0b010 -> {
                        //SLTI
                        outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "slti", rdConvert(rd), rdConvert(rs1), shamt).getBytes());

                        return;
                    }

                    case 0b011 -> {
                        //SLTIU
                        outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "sltiu", rdConvert(rd), rdConvert(rs1), shamt).getBytes());

                        return;
                    }

                    case 0b100 -> {
                        //XORI
                        outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "xori", rdConvert(rd), rdConvert(rs1), imm).getBytes());

                        return;
                    }
                    case 0b110 -> {
                        //ORI
                        outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "ori", rdConvert(rd), rdConvert(rs1), imm).getBytes());

                        return;
                    }
                    case 0b111 -> {
                        //ANDI
                        outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "andi", rdConvert(rd), rdConvert(rs1), imm).getBytes());

                        return;
                    }
                }


                if (funct7 == 0 && func == 0b001) {
                    //SLLI
                    outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "slli", rdConvert(rd), rdConvert(rs1), shamt).getBytes());
                    return;
                }
                if (funct7 == 0 && (func == (0b101))) {
                    //SRLI
                    outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "srli", rdConvert(rd), rdConvert(rs1), shamt).getBytes());
                    return;
                }
                if (funct7 == 0b0100000 && func == 0b101) {
                    //SRAI
                    outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, "srai", rdConvert(rd), rdConvert(rs1), shamt).getBytes());
                    return;
                }
            }
            invalidInstruction(addr, code, needPrint);
        }

        private void ADD_AND(int addr, int code, boolean needPrint) throws IOException {
            int rd = (code & 0b111110000000) >> 7;
            int rs1 = (code & 0b11111000000000000000) >> 15;
            int func = (code & 0b111000000000000) >> 12;
            int rs2 = (code & 0b1111100000000000000000000) >> 20;
            int funct7 = (code & 0b11111110000000000000000000000000) >> 25;
            String name = "invalid_instruction";
            if (funct7 == 0b0 && func == 0b0) {
                //ADD
                name = "add";
            }
            if (funct7 == 0b0100000 && func == 0b0) {
                //SUB
                name = "sub";
            }
            if (funct7 == 0b0 && func == 0b1) {
                //SLL
                name = "sll";
            }
            if (funct7 == 0b0 && func == 0b010) {
                //SLT
                name = "slt";
            }
            if (funct7 == 0b0 && func == 0b011) {
                //SLTU
                name = "sltu";
            }
            if (funct7 == 0b0 && func == 0b100) {
                //XOR
                name = "xor";
            }
            if (funct7 == 0b0 && func == 0b101) {
                //SRL
                name = "srl";
            }
            if (funct7 == 0b0100000 && func == 0b101) {
                //SRA
                name = "sra";
            }
            if (funct7 == 0b0 && func == 0b110) {
                //OR
                name = "or";
            }
            if (funct7 == 0 && func == 0b111) {
                //AND
                name = "and";
            }
            if (funct7 == 1 && func == 0) {
                name = "mul";
            }
            if (funct7 == 1 && func == 1) {
                name = "mulh";
            }
            if (funct7 == 1 && func == 0b10) {
                name = "mulhsu";
            }
            if (funct7 == 1 && func == 0b11) {
                name = "mulhu";
            }
            if (funct7 == 1 && func == 0b100) {
                name = "div";
            }
            if (funct7 == 1 && func == 0b101) {
                name = "divu";
            }
            if (funct7 == 1 && func == 0b110) {
                name = "rem";
            }
            if (funct7 == 1 && func == 0b111) {
                name = "remu";
            }
            if (name.equals("invalid_instruction")) {
                invalidInstruction(addr, code, needPrint);
                return;
            }
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s, %s\n", addr, code, name, rdConvert(rd), rdConvert(rs1), rdConvert(rs2)).getBytes());
            }
        }

        private String getCharString(int elem) {
            StringBuilder ans = new StringBuilder();
            if ((elem & 0b1000) != 0) {
                ans.append("i");
            }
            if ((elem & 0b100) != 0) {
                ans.append("o");
            }
            if ((elem & 0b10) != 0) {
                ans.append("r");
            }
            if ((elem & 0b1) != 0) {
                ans.append("w");
            }
            return ans.toString();
        }

        private void FENCE_PAUSE(int addr, int code, boolean needPrint) throws IOException {
            String name = "fence";
            if (code == 0b10000011001100000000000000001111) {
                name = "fence.tso";
            }
            if (code == 0b00000001000000000000000000001111) {
                name = "pause";
            }
            int successor = (code & 0b111100000000000000000000) >> 20;
            int predecessor = (code & 0b1111000000000000000000000000) >> 24;
            String successorString = getCharString(successor);
            String predecessorString = getCharString(predecessor);

            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%7s\t%s, %s\n", addr, code, name, successorString, predecessorString).getBytes());
            }
        }

        private void ECALL_BREAK(int addr, int code, boolean needPrint) throws IOException {
            if (needPrint) {
                if (code == 0b00000000000000000000000001110011) {
                    outputStream.write(String.format("   %05x:\t%08x\t%7s\n", addr, code, "ecall").getBytes());
                } else {
                    outputStream.write(String.format("   %05x:\t%08x\t%7s\n", addr, code, "ebreak").getBytes());
                }
            }
        }

        private void invalidInstruction(int addr, int code, boolean needPrint) throws IOException {
            if (needPrint) {
                outputStream.write(String.format("   %05x:\t%08x\t%-7s\n", addr, code, "invalid_instruction").getBytes());
            }
        }

        private void parseText(boolean needPrint) throws IOException {
            for (int i = 0; i < textLinesCount; ++i) {
                int code = bytesToInt(i * 4 + textOffset, 4);
                int addr = textAddr + i * 4;
                if (needPrint && functionNames.containsKey(addr)) {
                    outputStream.write(String.format("\n%08x \t<%s>:\n", addr, functionNames.get(addr)).getBytes());
                }
                switch (code & 0b1111111) {
                    case 0b0110111 -> LUI(addr, code, needPrint);
                    case 0b0010111 -> AUIPC(addr, code, needPrint);
                    case 0b1101111 -> JAL(addr, code, needPrint);
                    case 0b1100111 -> JALR(addr, code, needPrint);
                    case 0b1100011 -> B(addr, code, needPrint);
                    case 0b0000011 -> L(addr, code, needPrint);
                    case 0b0100011 -> S(addr, code, needPrint);
                    case 0b0010011 -> ADDI_SRAI(addr, code, needPrint);
                    case 0b0110011 -> ADD_AND(addr, code, needPrint);
                    case 0b0001111 -> FENCE_PAUSE(addr, code, needPrint);
                    case 0b1110011 -> ECALL_BREAK(addr, code, needPrint);
                    default -> invalidInstruction(addr, code, needPrint);
                }
            }
        }

        private void parseSymTab(boolean needPrint) throws IOException {
            if (needPrint) {
                outputStream.write("Symbol Value              Size Type     Bind     Vis       Index Name\n".getBytes());
            }
            int varCount = symtabSize / symtabLineSize;
            for (int i = 0; i < varCount; ++i) {
                // parse name
                int now = symtabOffset + i * symtabLineSize;
                int offsetInStrTab = bytesToInt(now, 4);
                String varName = bytestoString(strTabOffset + offsetInStrTab);
                int varValue = bytesToInt(now + 4, 4);
                int varSize = bytesToInt(now + 8, 4);
                int varInfo = bytesToInt(now + 12, 1);
                int varOther = bytesToInt(now + 13, 1);
                int varShndx = bytesToInt(now + 14, 2);
                String varIndex = INDEX.get(varShndx);
                if (varIndex == null) {
                    varIndex = String.valueOf(varShndx);
                }
                String varBind = BIND.get((varInfo) >> 4);
                String varType = TYPE.get((varInfo) & 0xf);
                String varVisibility = VISIBILITY.get((varOther) & 0x3);
                if (needPrint) {
                    outputStream.write(String.format("[%4d] 0x%-15X %5d %-8s %-8s %-8s %6s %s\n", i, varValue, varSize, varType, varBind, varVisibility, varIndex, varName).getBytes());
                } else {
                    if (Objects.equals(varType, "FUNC")) {
                        functionNames.put(varValue, varName);
                    }
                }
            }
        }

        public void parseElf() throws IOException {
            TYPE.put(0, "NOTYPE");
            TYPE.put(1, "OBJECT");
            TYPE.put(2, "FUNC");
            TYPE.put(3, "SECTION");
            TYPE.put(4, "FILE");
            TYPE.put(5, "COMMON");
            TYPE.put(6, "TLS");
            TYPE.put(10, "LOOS");
            TYPE.put(12, "HIOS");
            TYPE.put(13, "LOPROC");
            TYPE.put(15, "HIPROC");
            sectionHeadderOffset = bytesToInt(32, 4);
            sectionNameIndexInSectionHeadder = bytesToInt(50, 2);
            int now = sectionHeadderOffset;
            sectionNameOffset = bytesToInt(sectionHeadderOffset + sectionHeadderSize * sectionNameIndexInSectionHeadder + 16, 4);
            sectionHeadersCount = bytesToInt(48, 2);
            while (sectionHeadersCount-- > 0) {
                int shname = (bytesToInt(now, 4));
                String sectionName = bytestoString(shname + sectionNameOffset);
                if (sectionName.equals(".symtab")) {
                    symtabOffset = bytesToInt(now + 16, 4);
                    symtabSize = bytesToInt(now + 20, 4);
                }
                if (sectionName.equals(".strtab")) {
                    strTabOffset = bytesToInt(now + 16, 4);
                    strtabSize = bytesToInt(now + 20, 4);
                }
                if (sectionName.equals(".text")) {
                    textOffset = bytesToInt(now + 16, 4);
                    textSize = bytesToInt(now + 20, 4);
                    textAddr = bytesToInt(now + 12, 4);

                }
                now += sectionHeadderSize;
            }
            symtabLineSize = 16;
            textLinesCount = textSize / 4;
            parseSymTab(false);
            parseText(false);
            outputStream.write(".text\n".getBytes());
            parseText(true);
            outputStream.write("\n\n.symtab\n\n".getBytes());
            parseSymTab(true);

        }
    }
}
